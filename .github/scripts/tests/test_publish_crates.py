"""Release safety and recovery tests; no registry credentials or uploads."""

import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import urllib.error


def load(name):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).parents[1] / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


release = load("publish_crates")
ci = load("release_ci")
HEAD = "a" * 40
PACKAGES = [{"name": "base", "version": "1.0.0", "manifest": "base/Cargo.toml", "dependencies": []},
            {"name": "consumer", "version": "1.0.0", "manifest": "consumer/Cargo.toml", "dependencies": ["base"]}]


def receipt():
    return {"schema_version": 1, "repository": release.REPOSITORY, "commit": HEAD, "tree": "tree",
            "verification_passed": True,
            "packages": [dict(p, registry_status="absent", result="verified") for p in PACKAGES]}


def metadata():
    packages = [dict(id=n, name=n, version="1.0.0", manifest_path=f"/source/{n}/Cargo.toml",
                     publish=None, dependencies=[]) for n in ("consumer", "base", "private")]
    packages[0]["dependencies"] = [{"name": "base", "path": "/source/base", "req": "^1.0.0", "kind": "dev", "optional": True}]
    packages[2]["publish"] = []
    return {"packages": packages, "workspace_members": [p["id"] for p in packages]}


class OrderTests(unittest.TestCase):
    def test_metadata_discovers_members_and_orders_optional_dev_dependencies(self):
        result = release.ordered_packages(metadata(), Path('/source'))
        self.assertEqual([p['name'] for p in result], ['base', 'consumer'])

    def test_cycles_and_excluded_local_dependencies_fail(self):
        data = metadata()
        data['packages'][1]['dependencies'] = [{'name': 'consumer', 'path': '/source/consumer', 'req': '^1.0.0'}]
        with self.assertRaisesRegex(release.ReleaseError, 'cycle'):
            release.ordered_packages(data, Path('/source'))
        data = metadata()
        data['packages'][0]['dependencies'][0]['path'] = '/source/private'
        with self.assertRaisesRegex(release.ReleaseError, 'excluded'):
            release.ordered_packages(data, Path('/source'))

    def test_other_registry_only_is_excluded(self):
        data = metadata()
        data['packages'][2]['publish'] = ['private-registry']
        self.assertEqual(len(release.ordered_packages(data, Path('/source'))), 2)


class ReceiptTests(unittest.TestCase):
    def test_invalid_receipts_fail_closed(self):
        mutations = [lambda r: r.update(commit='b' * 40), lambda r: r.update(tree='other'),
                     lambda r: r.update(repository='other/common'), lambda r: r.update(schema_version=2),
                     lambda r: r.update(verification_passed=False),
                     lambda r: r['packages'].reverse(), lambda r: r['packages'][0].update(version='2.0.0'),
                     lambda r: r['packages'][0].update(registry_status='yanked'),
                     lambda r: r['packages'][0].update(result='remaining'),
                     lambda r: r['packages'][0].update(dependencies=['changed'])]
        with tempfile.TemporaryDirectory() as temp, patch.object(release, 'check_checkout'), patch.object(release, 'git', return_value='tree'):
            path = Path(temp) / 'receipt.json'
            path.write_text(json.dumps(receipt()))
            release.read_verified(path, Path('/source'), HEAD, PACKAGES)
            for mutate in mutations:
                changed = receipt()
                mutate(changed)
                path.write_text(json.dumps(changed))
                with self.assertRaises(release.ReleaseError):
                    release.read_verified(path, Path('/source'), HEAD, PACKAGES)
            for contents in ('{', '{}', 'null'):
                path.write_text(contents)
                with self.assertRaises(release.ReleaseError):
                    release.read_verified(path, Path('/source'), HEAD, PACKAGES)

    def test_dirty_or_changed_checkout_rejected(self):
        with patch.object(release, 'git', side_effect=[HEAD, ' M Cargo.toml']):
            with self.assertRaisesRegex(release.ReleaseError, 'clean'):
                release.check_checkout(Path('/source'), HEAD)
        with patch.object(release, 'git', return_value='b' * 40):
            with self.assertRaisesRegex(release.ReleaseError, 'changed'):
                release.check_checkout(Path('/source'), HEAD)


class RegistryTests(unittest.TestCase):
    def test_only_404_means_absent_and_error_body_is_retained(self):
        for status in (401, 403, 429, 500):
            error = urllib.error.HTTPError('https://crates.io/example', status, 'failure', {}, io.BytesIO(b'complete registry failure detail'))
            with patch.object(release.urllib.request, 'urlopen', side_effect=error):
                with self.assertRaisesRegex(release.ReleaseError, 'complete registry failure detail'):
                    release.request_json('https://crates.io/example', absent_ok=True)
            error.close()
        error = urllib.error.HTTPError('https://crates.io/example', 404, 'missing', {}, io.BytesIO())
        with patch.object(release.urllib.request, 'urlopen', side_effect=error):
            self.assertIsNone(release.request_json('https://crates.io/example', absent_ok=True))
        error.close()

    def test_malformed_and_yanked_versions_rejected(self):
        for record in ({'num': '1.0.0'}, {'num': 'other', 'yanked': False}, {'num': '1.0.0', 'yanked': True}):
            with patch.object(release, 'request_json', return_value={'version': record}):
                with self.assertRaises(release.ReleaseError):
                    release.registry_record('base', '1.0.0')

    def test_waits_for_index_before_dependents(self):
        with patch.object(release, 'registry_record', return_value={'yanked': False}), patch.object(release, 'index_available', side_effect=[False, True]), patch.object(release.time, 'sleep') as sleep:
            release.wait_available('base', '1.0.0')
            sleep.assert_called_once_with(5)

    def test_wait_timeout_and_registry_error_stop(self):
        with patch.object(release, 'registry_record', return_value=None):
            with self.assertRaisesRegex(release.ReleaseError, 'Timed out'):
                release.wait_available('base', '1.0.0', timeout=0)
        with patch.object(release, 'registry_record', side_effect=release.ReleaseError('registry down')):
            with self.assertRaisesRegex(release.ReleaseError, 'registry down'):
                release.wait_available('base', '1.0.0')

    def test_new_upload_requires_correct_trusted_attribution(self):
        good = {'provider': 'github', 'repository': release.REPOSITORY, 'run_id': 10, 'sha': HEAD}
        release.require_attribution({'trustpub_data': good}, '10', HEAD)
        for key, value in (('provider', 'gitlab'), ('repository', 'other/common'), ('run_id', 11), ('sha', 'b' * 40)):
            bad = dict(good, **{key: value})
            with self.assertRaisesRegex(release.ReleaseError, 'attribution'):
                release.require_attribution({'trustpub_data': bad}, '10', HEAD)
        with self.assertRaises(release.ReleaseError):
            release.require_attribution({}, '10', HEAD)


class ReleaseTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.output = Path(self.temp.name) / 'progress.json'
        for name, value in (('git', HEAD), ('check_checkout', None), ('release_packages', PACKAGES), ('read_verified', receipt())):
            patcher = patch.object(release, name, return_value=value)
            patcher.start()
            self.addCleanup(patcher.stop)

    def run_publish(self):
        release.run_release(Path('/source'), 'publish', self.output, '/verified.json', '10')

    def test_verify_unpublished_packages_together(self):
        with patch.object(release, 'registry_record', return_value=None), patch.object(release.subprocess, 'run') as run:
            release.run_release(Path('/source'), 'verify', self.output)
        command = run.call_args.args[0]
        self.assertIn('--dry-run', command)
        self.assertIn('--locked', command)
        self.assertEqual(command.count('--package'), 2)
        self.assertTrue(json.loads(self.output.read_text())['verification_passed'])

    def test_verify_does_not_overlay_already_published_dependencies(self):
        with patch.object(release, 'registry_record', side_effect=[{}, None]), patch.object(release.subprocess, 'run') as run:
            release.run_release(Path('/source'), 'verify', self.output)
        command = run.call_args.args[0]
        selected = [command[i + 1] for i, arg in enumerate(command) if arg == '--package']
        self.assertEqual(selected, ['consumer'])
        progress = json.loads(self.output.read_text())
        self.assertEqual([p['registry_status'] for p in progress['packages']], ['available', 'absent'])
        self.assertTrue(progress['verification_passed'])

    def test_verify_all_published_does_not_select_cargo_default_packages(self):
        with patch.object(release, 'registry_record', return_value={}), patch.object(release.subprocess, 'run') as run:
            release.run_release(Path('/source'), 'verify', self.output)
        run.assert_not_called()
        self.assertTrue(json.loads(self.output.read_text())['verification_passed'])

    def test_failed_package_verification_cannot_issue_successful_receipt(self):
        with patch.object(release, 'registry_record', side_effect=[{}, None]), patch.object(release.subprocess, 'run', side_effect=subprocess.CalledProcessError(101, 'cargo')):
            with self.assertRaises(subprocess.CalledProcessError):
                release.run_release(Path('/source'), 'verify', self.output)
        self.assertFalse(json.loads(self.output.read_text())['verification_passed'])

    def test_partial_publish_retains_progress_and_stops(self):
        with patch.object(release, 'registry_record', return_value=None), patch.object(release, 'wait_available') as wait, patch.object(release.subprocess, 'run', side_effect=[None, subprocess.CalledProcessError(101, 'cargo')]) as run:
            with self.assertRaises(subprocess.CalledProcessError):
                self.run_publish()
        progress = json.loads(self.output.read_text())
        self.assertEqual([p['result'] for p in progress['packages']], ['published', 'upload_started'])
        self.assertIn('error', progress)
        wait.assert_called_once_with('base', '1.0.0', '10', HEAD)
        self.assertEqual(run.call_count, 2)
        for call in run.call_args_list:
            self.assertIn('--no-verify', call.args[0])
            self.assertIn('--locked', call.args[0])
            self.assertNotIn('--dry-run', call.args[0])

    def test_resume_skips_available_version(self):
        verified = receipt()
        verified['packages'][0]['registry_status'] = 'available'
        with patch.object(release, 'read_verified', return_value=verified), patch.object(release, 'registry_record', side_effect=[{}, None, {}, None]), patch.object(release, 'wait_available') as wait, patch.object(release.subprocess, 'run') as run:
            self.run_publish()
        run.assert_called_once()
        self.assertIn('/source/consumer/Cargo.toml', run.call_args.args[0])
        self.assertEqual(wait.call_count, 2)
        self.assertEqual([p['result'] for p in json.loads(self.output.read_text())['packages']], ['previously_available', 'published'])

    def test_registry_changes_after_verification_stop_before_any_upload(self):
        for statuses in ([{}, None], [None, {}]):
            with self.subTest(statuses=statuses), patch.object(release, 'registry_record', side_effect=statuses + [None, None]), patch.object(release, 'wait_available'), patch.object(release.subprocess, 'run') as run:
                with self.assertRaisesRegex(release.ReleaseError, 'changed after verification'):
                    self.run_publish()
                run.assert_not_called()

    def test_version_appearing_at_upload_time_requires_verification_again(self):
        with patch.object(release, 'registry_record', side_effect=[None, None, {}, None]), patch.object(release, 'wait_available'), patch.object(release.subprocess, 'run') as run:
            with self.assertRaisesRegex(release.ReleaseError, 'changed after verification'):
                self.run_publish()
        run.assert_not_called()

    def test_previously_available_version_disappearing_stops_publication(self):
        verified = receipt()
        verified['packages'][0]['registry_status'] = 'available'
        with patch.object(release, 'read_verified', return_value=verified), patch.object(release, 'registry_record', side_effect=[{}, None, None, None]), patch.object(release, 'wait_available'), patch.object(release.subprocess, 'run') as run:
            with self.assertRaisesRegex(release.ReleaseError, 'changed after verification'):
                self.run_publish()
        run.assert_not_called()

    def test_registry_failure_stops_before_upload(self):
        with patch.object(release, 'registry_record', side_effect=release.ReleaseError('HTTP 500 full detail')), patch.object(release.subprocess, 'run') as run:
            with self.assertRaisesRegex(release.ReleaseError, 'full detail'):
                self.run_publish()
        run.assert_not_called()
        self.assertIn('full detail', json.loads(self.output.read_text())['error'])

    def test_unconfirmed_upload_is_preserved(self):
        with patch.object(release, 'registry_record', return_value=None), patch.object(release, 'wait_available', side_effect=release.ReleaseError('wrong attribution')), patch.object(release.subprocess, 'run') as run:
            with self.assertRaisesRegex(release.ReleaseError, 'attribution'):
                self.run_publish()
        run.assert_called_once()
        self.assertEqual(json.loads(self.output.read_text())['packages'][0]['result'], 'uploaded_unconfirmed')

    def test_bad_receipt_prevents_upload(self):
        with patch.object(release, 'read_verified', side_effect=release.ReleaseError('invalid receipt')), patch.object(release.subprocess, 'run') as run:
            with self.assertRaises(release.ReleaseError):
                self.run_publish()
        run.assert_not_called()

    def test_confirmation_checks_partial_progress(self):
        data = dict(receipt(), run_id='10')
        data['packages'][0]['result'] = 'published'
        data['packages'][1]['result'] = 'remaining'
        with patch.object(release, 'wait_available') as wait:
            with self.assertRaisesRegex(release.ReleaseError, 'consumer'):
                release.confirm(data, '10', HEAD)
        wait.assert_called_once_with('base', '1.0.0', '10', HEAD)


class CiTests(unittest.TestCase):
    def run_data(self, **kwargs):
        return dict(id=1, head_sha=HEAD, head_branch='main', event='push', name='CI', run_number=1, run_attempt=1, status='completed', conclusion='success', html_url='https://github.com/run', **kwargs)

    def test_exact_main_ci_and_aggregate_required(self):
        good = self.run_data()
        job = {'name': 'test success', 'status': 'completed', 'conclusion': 'success'}
        with patch.object(ci, 'gh_pages', side_effect=[[{'workflow_runs': [good]}], [{'jobs': [job]}]]) as api:
            ci.require_ci(ci.REPOSITORY, HEAD)
        self.assertIn('workflows/ci.yml/runs', api.call_args_list[0].args[0])
        self.assertIn('/attempts/1/jobs', api.call_args_list[1].args[0])
        for field, value in (('head_sha', 'b' * 40), ('head_branch', 'feature'), ('event', 'pull_request'), ('name', 'Verify wallet libraries'), ('conclusion', 'failure'), ('status', 'in_progress')):
            with patch.object(ci, 'gh_pages', return_value=[{'workflow_runs': [dict(good, **{field: value})]}]):
                with self.assertRaises(ValueError):
                    ci.require_ci(ci.REPOSITORY, HEAD)
        for jobs in ([], [dict(job, conclusion='skipped')], [dict(job, conclusion='failure')], [job, job]):
            with patch.object(ci, 'gh_pages', side_effect=[[{'workflow_runs': [good]}], [{'jobs': jobs}] ]):
                with self.assertRaises(ValueError):
                    ci.require_ci(ci.REPOSITORY, HEAD)

    def test_environment_missing_or_weakened_is_rejected(self):
        env = {"can_admins_bypass": False,
               "deployment_branch_policy": {"protected_branches": False, "custom_branch_policies": True},
               "protection_rules": [{"type": "required_reviewers", "prevent_self_review": False,
                                     "reviewers": [{"type": "User", "reviewer": {"login": "ebfull"}}]}]}
        branches = [{"branch_policies": [{"name": "main", "type": "branch"}]}]
        with patch.object(ci, 'gh_pages', side_effect=[[env], branches]):
            ci.require_environment(ci.REPOSITORY)
        for changed in (dict(env, can_admins_bypass=True), dict(env, protection_rules=[]),
                        dict(env, deployment_branch_policy=None)):
            with patch.object(ci, 'gh_pages', side_effect=[[changed], branches]):
                with self.assertRaises(ValueError):
                    ci.require_environment(ci.REPOSITORY)
        for policies in ([], [{"name": "*", "type": "branch"}],
                         [{"name": "main", "type": "tag"}],
                         [{"name": "main", "type": "branch"}, {"name": "dev", "type": "branch"}]):
            with patch.object(ci, 'gh_pages', side_effect=[[env], [{"branch_policies": policies}]]):
                with self.assertRaises(ValueError):
                    ci.require_environment(ci.REPOSITORY)

    def test_newer_failed_attempt_cannot_use_older_success(self):
        good = self.run_data()
        failed = dict(good, run_attempt=2, conclusion='failure')
        with patch.object(ci, 'gh_pages', return_value=[{'workflow_runs': [good, failed]}]):
            with self.assertRaises(ValueError):
                ci.require_ci(ci.REPOSITORY, HEAD)


if __name__ == '__main__':
    unittest.main()
