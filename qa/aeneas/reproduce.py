#!/usr/bin/env python3
"""Extract pinned Common field arithmetic and check every catalogued Lean proof."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
import tomllib


HERE = Path(__file__).resolve().parent
PIN = json.loads((HERE / "provenance.json").read_text())
CATALOG = json.loads((HERE / "catalog.json").read_text())
if CATALOG["modules"][-1] != CATALOG["census_module"]:
    raise RuntimeError("The census must be compiled after every proof module")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_command(arguments, cwd):
    return subprocess.check_output(arguments, cwd=cwd, text=True).strip()


def check_proof_census(proof_log, catalog):
    if "sorryAx" in proof_log or re.search(r"\berror:", proof_log):
        raise RuntimeError("The proof log contains an error or sorryAx")
    for theorem in catalog["proved"]:
        declaration = re.escape("'" + theorem + "'")
        dependencies = re.findall(
            declaration + r" depends on axioms:\s*\[([^]]*)\]", proof_log
        )
        independent = re.findall(
            declaration + r" does not depend on any axioms", proof_log
        )
        if len(dependencies) + len(independent) != 1:
            raise RuntimeError("Missing or duplicate proof trust census for " + theorem)
        actual = {item.strip() for item in dependencies[0].split(",") if item.strip()} \
            if dependencies else set()
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        allowed.update(catalog.get("type_only_axioms", {}).get(theorem, []))
        if not actual <= allowed:
            raise RuntimeError(f"Unexpected proof trust census for {theorem}: {actual}")



def make_slice(repo, destination):
    source = repo / "crates/udon/src/field/pasta"
    parameters = (source / "parameters.rs").read_text()
    primes = re.findall(
        r'    (PallasBase|PallasScalar),\n    modulus: "(0x[0-9a-f]+)"', parameters
    )
    if len(primes) != 2:
        raise RuntimeError("Could not identify both pinned Pasta moduli")
    lines = [
        "#![no_std]",
        "#![forbid(unsafe_code)]",
        "pub mod field {",
        "pub mod pasta {",
        "pub trait PrimeModulus {",
        "    const MODULUS: [u64; 4];",
        "    const TWICE_MODULUS: [u64; 4];",
        "    const MONTGOMERY_INV: u64;",
        "}",
    ]
    radix = 1 << 64

    def limbs(value):
        return "[" + ", ".join(hex((value >> (64 * i)) % radix) for i in range(4)) + "]"

    for marker, literal in primes:
        modulus = int(literal, 16)
        coefficient = -pow(modulus % radix, -1, radix) % radix
        assert ((modulus % radix) * coefficient + 1) % radix == 0
        assert modulus >> 128 == 1 << 126
        assert 3 * modulus < 1 << 256
        lines.extend([
            f"#[derive(Clone, Copy)] pub enum {marker} {{}}",
            f"impl PrimeModulus for {marker} {{",
            f"    const MODULUS: [u64; 4] = {limbs(modulus)};",
            f"    const TWICE_MODULUS: [u64; 4] = {limbs(2 * modulus)};",
            f"    const MONTGOMERY_INV: u64 = {hex(coefficient)};",
            "}",
        ])
    for name in ["word", "montgomery"]:
        lines.append(f"#[path = {json.dumps(str(source / (name + '.rs')))}] pub mod {name};")
    lines.extend(["}", "}"])
    destination.write_text("\n".join(lines) + "\n")



def check_native_lock(repo, wrapper, package_name="udon-native-field-proof"):
    original = tomllib.loads((repo / "Cargo.lock").read_text())
    actual = tomllib.loads((wrapper / "Cargo.lock").read_text())
    fields = ["name", "version", "source", "checksum"]
    pinned = {tuple(package.get(key) for key in fields) for package in original["package"]}
    for package in actual["package"]:
        if package["name"] == package_name:
            continue
        if tuple(package.get(key) for key in fields) not in pinned:
            raise RuntimeError("Unpinned native extraction dependency: " + package["name"])


def check_ordering(llbc):
    name = [{"Ident": [part, 0]} for part in ["core", "cmp", "Ordering"]]
    declaration = next(item for item in llbc["translated"]["type_decls"]
                       if item and item["item_meta"]["name"] == name)
    variants = declaration["kind"]["Enum"]
    actual = [(item["name"], item["discriminant"]) for item in variants]
    expected = [("Less", {"Signed": ["I8", "-1"]}),
                ("Equal", {"Signed": ["I8", "0"]}),
                ("Greater", {"Signed": ["I8", "1"]})]
    if actual != expected:
        raise RuntimeError("Unexpected Rust Ordering discriminants: " + repr(actual))



def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=HERE.parents[1])
    parser.add_argument("--tools", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True,
                        help="New output directory; must not already exist")
    parser.add_argument("--offline", action="store_true")
    parser.add_argument("--prepare-only", action="store_true",
                        help="Prepare sources without claiming checked proofs")
    parser.add_argument("--native-charon", type=Path, help="Verified patched compiler build")
    args = parser.parse_args()
    repo = args.repo.resolve()
    tools = args.tools.resolve()
    backend = tools / "backends/lean"
    head = read_command(["git", "rev-parse", "HEAD"], repo)
    subprocess.run(["git", "merge-base", "--is-ancestor", PIN["common_revision"], head],
                   cwd=repo, check=True)
    for relative, expected in PIN["source_hashes"].items():
        if digest(repo / relative) != expected:
            raise RuntimeError("Production source differs from the pin: " + relative)
    for relative, expected in PIN["tool_hashes"].items():
        if digest(tools / relative) != expected:
            raise RuntimeError("Tool differs from the pin: " + relative)
    aeneas_version = read_command([str(tools / "aeneas"), "-version"], repo)
    charon_version = read_command([str(tools / "charon"), "version"], repo)
    if PIN["aeneas_release"] not in aeneas_version:
        raise RuntimeError("Unexpected Aeneas version")
    if PIN["charon_revision"] not in charon_version:
        raise RuntimeError("Unexpected Charon version")
    native_charon = tools / "charon"
    native_manifest = None
    if CATALOG.get("native_charon_patched"):
        if args.native_charon is None:
            raise RuntimeError("Build the pinned native compiler and pass --native-charon")
        from build_native_charon import verify_manifest
        native_manifest = verify_manifest(args.native_charon.resolve())
        native_charon = args.native_charon.resolve() / "build/release/charon"
        version = read_command([str(native_charon), "version"], repo)
        if PIN["charon_native"]["revision_label"] not in version:
            raise RuntimeError("Unexpected native Charon version")
    lean_toolchain = (backend / "lean-toolchain").read_text().strip()
    if lean_toolchain != "leanprover/lean4:v" + PIN["lean_version"]:
        raise RuntimeError("Unexpected Lean toolchain")
    manifest = json.loads((backend / "lake-manifest.json").read_text())
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    if mathlib["rev"] != PIN["mathlib_revision"]:
        raise RuntimeError("Unexpected Mathlib revision")
    sysroot = Path(read_command(["rustup", "run", PIN["rust_toolchain"], "rustc",
                                "--print", "sysroot"], repo))
    std_source = sysroot / PIN["rust_std"]["path_from_sysroot"]
    if digest(std_source) != PIN["rust_std"]["sha256"]:
        raise RuntimeError("The Rust carry/borrow helper source differs from the pin")
    for relative, expected_hash in PIN.get("rust_iterator_sources", {}).items():
        if digest(sysroot / relative) != expected_hash:
            raise RuntimeError("Rust iterator source differs from the pin: " + relative)
    rust_version = read_command(["rustup", "run", PIN["rust_toolchain"], "rustc", "-Vv"], repo)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    for directory in ["logs", "llbc", "lean", "slice"]:
        (output / directory).mkdir()
    environment = os.environ.copy()
    environment["CARGO_TARGET_DIR"] = str(output / "cargo-target")
    environment["RUST_MIN_STACK"] = "67108864"
    stages = []
    result = {
        "status": "preparing", "proofs_checked": False,
        "common_revision": head, "production_revision": PIN["common_revision"],
        "aeneas_version": aeneas_version, "charon_version": charon_version,
        "lean_toolchain": lean_toolchain, "rust_version": rust_version,
        "source_hashes": PIN["source_hashes"], "rust_std": PIN["rust_std"],
        "stages": stages, "native_charon_manifest": native_manifest,
    }

    def save():
        temporary = output / "results.tmp"
        temporary.write_text(json.dumps(result, indent=2) + "\n")
        temporary.replace(output / "results.json")

    def run(name, arguments, cwd):
        log = output / "logs" / (name + ".log")
        started = time.monotonic()
        with log.open("w") as stream:
            process = subprocess.run(arguments, cwd=cwd, env=environment,
                                     stdout=stream, stderr=subprocess.STDOUT)
        elapsed = round(time.monotonic() - started, 3)
        stages.append({"name": name, "arguments": arguments, "cwd": str(cwd),
                       "exit_code": process.returncode, "seconds": elapsed, "log": str(log)})
        save()
        print(f"{name}: exit {process.returncode} ({elapsed}s)", flush=True)
        if process.returncode:
            print("\n".join(log.read_text().splitlines()[-35:]))
            raise RuntimeError("Stage failed; inspect " + str(log))

    save()
    try:
        run("word-charon", [str(tools / "charon"), "cargo", "--preset=aeneas",
            "--sysroot=default", "--start-from", "crate::field::pasta::word",
            "--rustc-arg=-Coverflow-checks=on", "--rustc-arg=-Cdebug-assertions=on",
            "--dest-file", str(output / "llbc/word.llbc"), "--", "--package",
            "zakura-udon", "--lib", "--locked", *(["--offline"] if args.offline else [])], repo)
        if json.loads((output / "llbc/word.llbc").read_text())["has_errors"]:
            raise RuntimeError("Charon exported a partial model")
        run("word-aeneas", [str(tools / "aeneas"), "-backend", "lean", "-split-files",
            "-subdir", "Word", "-no-progress-bar", "-abort-on-error", "-dest",
            str(output / "lean"), str(output / "llbc/word.llbc")], output)
        lean = output / "lean"
        template = lean / "Word/FunsExternal_Template.lean"
        external = set(re.findall(r"\baxiom\s+([A-Za-z0-9_.]+)", template.read_text()))
        expected = {"core.num.U64.carrying_add", "core.num.U64.borrowing_sub"}
        if external != expected:
            raise RuntimeError("Unexpected external models: " + repr(external))
        shutil.copyfile(HERE / "word_support/FunsExternal.lean", lean / "Word/FunsExternal.lean")
        template.unlink()
        model_modules = ["Word.Types", "Word.FunsExternal", "Word.Funs"]
        if CATALOG.get("kernel_slice"):
            slice_file = output / "slice/lib.rs"
            make_slice(repo, slice_file)
            run("slice-charon", [str(tools / "charon"), "rustc", "--preset=aeneas",
                "--sysroot=default", "--include", "core::cmp::*::is_lt",
                "--include", "core::num::*::wrapping_neg",
                "--rustc-arg=-Coverflow-checks=on", "--rustc-arg=-Cdebug-assertions=on",
                "--dest-file", str(output / "llbc/kernel-slice.llbc"), "--",
                "--crate-type", "lib", "--edition", "2024", "--crate-name", "udon_kernel_slice",
                str(slice_file)], output / "slice")
            data = json.loads((output / "llbc/kernel-slice.llbc").read_text())
            if data["has_errors"]:
                raise RuntimeError("Charon exported a partial Montgomery model")
            check_ordering(data)
            run("slice-aeneas", [str(tools / "aeneas"), "-backend", "lean", "-split-files",
                "-subdir", "KernelSlice", "-no-progress-bar", "-abort-on-error", "-dest",
                str(lean), str(output / "llbc/kernel-slice.llbc")], output)
            template = lean / "KernelSlice/FunsExternal_Template.lean"
            actual = set(re.findall(r"\baxiom\s+([A-Za-z0-9_.]+)", template.read_text()))
            if actual != expected:
                raise RuntimeError("Unexpected Montgomery external models: " + repr(actual))
            shutil.copyfile(HERE / "kernel_support/FunsExternal.lean",
                            lean / "KernelSlice/FunsExternal.lean")
            template.unlink()
            model_modules.extend(["KernelSlice.Types", "KernelSlice.FunsExternal", "KernelSlice.Funs"])
        if CATALOG.get("native_roots"):
            native = output / "native"
            (native / "src").mkdir(parents=True)
            (native / "Cargo.toml").write_text(
                '[package]\nname = "udon-native-field-proof"\nversion = "0.0.0"\n'
                'edition = "2024"\n\n[workspace]\n\n[dependencies]\n'
                'udon = { package = "zakura-udon", path = ' +
                json.dumps(str(repo / "crates/udon")) + ' }\n')
            shutil.copyfile(HERE / "native_wrapper.rs", native / "src/lib.rs")
            shutil.copyfile(repo / "Cargo.lock", native / "Cargo.lock")
            run("native-lock", ["cargo", "+" + PIN["rust_toolchain"], "metadata",
                                "--format-version=1", "--offline"], native)
            check_native_lock(repo, native)
            raw = output / "llbc/native-raw.llbc"
            command = [str(native_charon), "cargo", "--preset=aeneas", "--sysroot=default",
                "--consts=values", "--remove-adt-clauses", "--lift-associated-types=*",
                "--remove-unused-clauses"]
            for name in ["zakura_udon", "core::cmp::*::is_lt", "core::num::*::unsigned_abs",
                         "core::num::*::wrapping_neg", "core::num::*::wrapping_abs",
                         "core::num::*::is_negative", "zakura_bento_core::addchain", "core::mem::drop"]:
                command.extend(["--include", name])
            for root in CATALOG["native_roots"]:
                command.extend(["--start-from", "udon_native_field_proof::" + root])
            for root in CATALOG.get("native_private_roots", []):
                command.extend(["--start-from", root])
            command.extend(["--no-dedup-serialized-ast", "--rustc-arg=-Coverflow-checks=on",
                "--rustc-arg=-Cdebug-assertions=on", "--dest-file", str(raw), "--", "--lib",
                "--locked", *(["--offline"] if args.offline else [])])
            # macOS permits the larger main stack when set in the shell before exec.
            run("native-charon", ["/bin/zsh", "-c", 'ulimit -s 65520\nexec "$@"',
                                 "charon-main-stack", *command], native)
            data = json.loads(raw.read_text())
            if data["has_errors"]:
                raise RuntimeError("Charon exported a partial native model")
            check_ordering(data)
            previous = raw
            if CATALOG.get("native_merge_expansion"):
                if CATALOG["native_merge_expansion"] != 8:
                    raise RuntimeError("The merge adapter requires exactly eight words")
                adapted = output / "llbc/unroll-merge.llbc"
                run("native-unroll-merge", ["python3", str(HERE / "adapters/unroll_merge.py"),
                    str(previous), str(adapted), "--self-test"], output)
                previous = adapted
            for name in ["normalize_constants", "project_parameters", "mark_constant_effects",
                         *(["select_private_roots"] if CATALOG.get("native_private_roots") else [])]:
                adapted = output / "llbc" / (name + ".llbc")
                flags = ["--retain-callback-functions"] if name == "project_parameters" else []
                run(name, ["python3", str(HERE / "adapters" / (name + ".py")),
                           str(previous), str(adapted), *flags], output)
                previous = adapted
            if CATALOG.get("native_loop_marker_clones"):
                if CATALOG["native_loop_marker_clones"] != 1:
                    raise RuntimeError("The decoder adapter expects exactly one marker clone")
                adapted = output / "llbc/retain-loop-type.llbc"
                run("native-retain-loop-type", ["python3", str(HERE / "adapters/retain_loop_type.py"),
                    str(previous), str(adapted)], output)
                previous = adapted
            if CATALOG.get("native_difference_exit_hoists"):
                if CATALOG["native_difference_exit_hoists"] != 3:
                    raise RuntimeError("The product-difference adapter requires three exit continuations")
                adapted = output / "llbc/hoist-product-difference-exits.llbc"
                run("native-hoist-product-difference-exits", ["python3",
                    str(HERE / "adapters/hoist_product_difference_exits.py"),
                    str(previous), str(adapted), "--self-test"], output)
                previous = adapted
            run("native-aeneas", [str(tools / "aeneas"), "-backend", "lean", "-namespace", "NativeField",
                "-subdir", "NativeField", "-filter-trait-methods", "-split-files", "-no-progress-bar",
                "-abort-on-error", "-dest", str(lean), str(previous)], output)
            template = lean / "NativeField/FunsExternal_Template.lean"
            actual = set(re.findall(r"\baxiom\s+([A-Za-z0-9_.]+)", template.read_text()))
            native_expected = expected | {
                "core.marker.PhantomData.Insts.CoreCloneClone.clone",
                "core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next",
                "Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter",
                "MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter",
                "core.array.from_fn",
                "core.bool.Bool.then",
                "core.option.Option.Insts.CoreCmpPartialEqOption.eq",
                "core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice.next",
                "core.slice.Slice.chunks_exact_mut",
            }
            if CATALOG.get("native_loop_marker_clones"):
                native_expected |= {
                    "core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next",
                    "core.slice.iter.Chunks.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedSlice.next_back",
                    "core.slice.Slice.chunks",
                }
            if CATALOG.get("native_merge_expansion"):
                native_expected.add("MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter")
            if actual != native_expected:
                raise RuntimeError("Unexpected native external models: " + repr(actual))
            type_template = lean / "NativeField/TypesExternal_Template.lean"
            type_externals = set(re.findall(r"\baxiom\s+([A-Za-z0-9_.]+)", type_template.read_text()))
            native_types = {"core.array.iter.IntoIter", "core.slice.iter.ChunksExactMut"}
            if CATALOG.get("native_loop_marker_clones"):
                native_types.add("core.slice.iter.Chunks")
            if type_externals != native_types:
                raise RuntimeError("Unexpected native external types: " + repr(type_externals))
            shutil.copyfile(HERE / "native_support/TypesExternal.lean", lean / "NativeField/TypesExternal.lean")
            type_template.unlink()
            run("native-iterator-model", ["python3", str(HERE / "adapters/model_mutable_iterators.py"),
                str(lean / "NativeField/Funs.lean"), "--expected",
                str(CATALOG["native_mutable_zip_calls"]), "--chunks",
                str(CATALOG["native_chunk_zip_calls"]), "--expected-next",
                str(CATALOG.get("native_mutable_zip_next_calls", CATALOG["native_mutable_zip_calls"]))], output)
            if CATALOG.get("native_loop_marker_clones"):
                run("native-marker-type-argument", ["python3", str(HERE / "adapters/retain_loop_type.py"),
                    str(lean / "NativeField/Funs.lean"), "--lean"], output)
            if CATALOG.get("native_difference_exit_hoists"):
                run("native-apply-difference-back", ["python3",
                    str(HERE / "adapters/apply_difference_back.py"),
                    str(lean / "NativeField/Funs.lean")], output)
            shutil.copyfile(HERE / "native_support/FunsExternal.lean", lean / "NativeField/FunsExternal.lean")
            template.unlink()
            model_modules.extend(["NativeField.TypesExternal", "NativeField.Types", "NativeField.FunsExternal", "NativeField.Funs"])
        if CATALOG.get("sqrt_roots"):
            algorithms = output / "llbc/sqrt-algorithms-raw.llbc"
            run("sqrt-algorithms-charon", [str(tools / "charon"), "cargo",
                "--preset=aeneas", "--sysroot=default", "--include", "zakura_udon",
                "--start-from", "zakura_udon::field::pasta::algorithms::tonelli_shanks_with_roots",
                "--start-from", "zakura_udon::field::pasta::algorithms::tonelli_shanks_alt_with_roots",
                "--no-dedup-serialized-ast", "--rustc-arg=-Coverflow-checks=on",
                "--rustc-arg=-Cdebug-assertions=on", "--dest-file", str(algorithms),
                "--", "--package", "zakura-udon", "--lib", "--locked",
                *(["--offline"] if args.offline else [])], repo)
            if json.loads(algorithms.read_text())["has_errors"]:
                raise RuntimeError("Charon exported a partial square-root algorithm model")
            copied = output / "llbc/sqrt-algorithms.llbc"
            run("sqrt-algorithms-assert-copy", ["python3",
                str(HERE / "adapters/copy_bool_assertions.py"), str(algorithms), str(copied),
                "--expected", str(CATALOG["sqrt_algorithm_assert_copies"])], output)
            run("sqrt-algorithms-aeneas", [str(tools / "aeneas"), "-backend", "lean",
                "-namespace", "SqrtAlgorithms", "-subdir", "SqrtAlgorithms", "-split-files",
                "-filter-trait-methods", "-no-progress-bar", "-abort-on-error", "-dest",
                str(lean), str(copied)], output)
            (lean / "SqrtSupport").mkdir()
            shutil.copyfile(HERE / "sqrt_support/RangeContains.lean",
                            lean / "SqrtSupport/RangeContains.lean")
            template = lean / "SqrtAlgorithms/FunsExternal_Template.lean"
            external = set(re.findall(r"\baxiom\s+([A-Za-z0-9_.]+)", template.read_text()))
            if external != {"core.ops.range.RangeInclusive.contains"}:
                raise RuntimeError("Unexpected square-root algorithm external models")
            shutil.copyfile(HERE / "sqrt_algorithms_support/FunsExternal.lean",
                            lean / "SqrtAlgorithms/FunsExternal.lean")
            template.unlink()
            sqrt = output / "sqrt"
            (sqrt / "src").mkdir(parents=True)
            (sqrt / "Cargo.toml").write_text(
                '[package]\nname = "udon-sqrt-proof"\nversion = "0.0.0"\n'
                'edition = "2024"\n\n[workspace]\n\n[dependencies]\n'
                'udon = { package = "zakura-udon", path = ' +
                json.dumps(str(repo / "crates/udon")) + ' }\n')
            shutil.copyfile(HERE / "sqrt_wrapper.rs", sqrt / "src/lib.rs")
            shutil.copyfile(repo / "Cargo.lock", sqrt / "Cargo.lock")
            run("sqrt-lock", ["cargo", "+" + PIN["rust_toolchain"], "metadata",
                              "--format-version=1", "--offline"], sqrt)
            check_native_lock(repo, sqrt, "udon-sqrt-proof")
            raw = output / "llbc/sqrt-raw.llbc"
            command = [str(native_charon), "cargo", "--preset=aeneas", "--sysroot=default",
                "--consts=values", "--remove-adt-clauses", "--lift-associated-types=*",
                "--remove-unused-clauses"]
            for name in ["zakura_udon", "core::cmp::*::is_lt", "core::num::*::unsigned_abs",
                         "core::num::*::wrapping_neg", "core::num::*::wrapping_abs",
                         "core::num::*::is_negative"]:
                command.extend(["--include", name])
            command.extend(["--opaque",
                "zakura_udon::field::pasta::parameters::{impl zakura_udon::field::pasta::parameters::sealed::Parameters<_> for _}::pow_sqrt_exponent"])
            for root in CATALOG["sqrt_roots"]:
                command.extend(["--start-from", "udon_sqrt_proof::" + root])
            command.extend(["--no-dedup-serialized-ast", "--rustc-arg=-Coverflow-checks=on",
                "--rustc-arg=-Cdebug-assertions=on", "--dest-file", str(raw), "--", "--lib",
                "--locked", *(["--offline"] if args.offline else [])])
            run("sqrt-charon", ["/bin/zsh", "-c", 'ulimit -s 65520\nexec "$@"',
                               "charon-main-stack", *command], sqrt)
            data = json.loads(raw.read_text())
            if data["has_errors"]:
                raise RuntimeError("Charon exported a partial native square-root model")
            check_ordering(data)
            previous = raw
            for name in ["normalize_constants", "mark_constant_effects", "project_unused_parent",
                         "copy_bool_assertions"]:
                adapted = output / "llbc" / ("sqrt-" + name + ".llbc")
                flags = ["--expected", str(CATALOG["sqrt_native_assert_copies"])] \
                    if name == "copy_bool_assertions" else []
                run("sqrt-" + name, ["python3", str(HERE / "adapters" / (name + ".py")),
                                    str(previous), str(adapted), *flags], output)
                previous = adapted
            run("sqrt-aeneas", [str(tools / "aeneas"), "-backend", "lean", "-namespace",
                "SqrtNative", "-subdir", "SqrtNative", "-filter-trait-methods", "-split-files",
                "-no-progress-bar", "-abort-on-error", "-dest", str(lean), str(previous)], output)
            template = lean / "SqrtNative/FunsExternal_Template.lean"
            external = set(re.findall(r"\baxiom\s+([A-Za-z0-9_.]+)", template.read_text()))
            sqrt_expected = {
                "core.marker.PhantomData.Insts.CoreCloneClone.clone",
                "core.num.U64.carrying_add", "core.ops.range.RangeInclusive.contains",
                "core.option.Option.map",
                *["zakura_udon.field.pasta.parameters." + field +
                  ".Insts.Zakura_udonFieldPastaParametersSealedParameters" + field +
                  ".pow_sqrt_exponent" for field in ["PallasBase", "PallasScalar"]],
            }
            if external != sqrt_expected:
                raise RuntimeError("Unexpected native square-root external models")
            for namespace in ["SqrtAlgorithms", "SqrtNative"]:
                if (lean / namespace / "TypesExternal_Template.lean").exists():
                    raise RuntimeError("Unexpected square-root external types: " + namespace)
            shutil.copyfile(HERE / "sqrt_support/FunsExternal.lean",
                            lean / "SqrtNative/FunsExternal.lean")
            template.unlink()
            model_modules.extend(["SqrtSupport.RangeContains", "SqrtAlgorithms.Types",
                "SqrtAlgorithms.FunsExternal", "SqrtAlgorithms.Funs", "SqrtNative.Types",
                "SqrtNative.FunsExternal", "SqrtNative.Funs"])
        if CATALOG.get("large_sqrt_roots"):
            if CATALOG["large_sqrt_roots"] != CATALOG["sqrt_roots"]:
                raise RuntimeError("The large-table replay must cover the same six public square-root APIs")
            large = output / "large"
            (large / "src").mkdir(parents=True)
            (large / "Cargo.toml").write_text(
                '[package]\nname = "udon-sqrt-proof"\nversion = "0.0.0"\n'
                'edition = "2024"\n\n[workspace]\n\n[dependencies]\n'
                'udon = { package = "zakura-udon", features = ["sqrt-table-large"], path = ' +
                json.dumps(str(repo / "crates/udon")) + ' }\n')
            shutil.copyfile(HERE / "sqrt_wrapper.rs", large / "src/lib.rs")
            shutil.copyfile(repo / "Cargo.lock", large / "Cargo.lock")
            run("large-lock", ["cargo", "+" + PIN["rust_toolchain"], "metadata",
                               "--format-version=1", "--offline"], large)
            check_native_lock(repo, large, "udon-sqrt-proof")
            method_prefix = "zakura_udon::field::pasta::parameters::{impl zakura_udon::field::pasta::parameters::sealed::Parameters<_> for _}::"
            for namespace, label, adapters, roots, opaque, support, expected in [
                ("LargeAlgorithms", "large-algorithms", ["normalize_constants", "project_parameters"],
                 [f"{{impl zakura_udon::field::pasta::parameters::sealed::Parameters for zakura_udon::field::pasta::parameters::{field}}}::{method}"
                  for field in ["PallasBase", "PallasScalar"] for method in ["sqrt_large", "sqrt_finish_large"]],
                 ["pow_sqrt_exponent"], "large_support", {"core.bool.Bool.then", "core.num.U64.carrying_add"}),
                ("LargePublic", "large-public", ["normalize_constants", "project_unused_parent"],
                 ["udon_sqrt_proof"], ["pow_sqrt_exponent", "sqrt_large", "sqrt_finish_large"],
                 "large_public_support", {"core.num.U64.carrying_add",
                  *[f"zakura_udon.field.pasta.parameters.{field}.Insts.Zakura_udonFieldPastaParametersSealedParameters{field}.{method}"
                    for field in ["PallasBase", "PallasScalar"]
                    for method in ["pow_sqrt_exponent", "sqrt_large", "sqrt_finish_large"]]}),
            ]:
                raw = output / "llbc" / (label + "-raw.llbc")
                command = [str(native_charon), "cargo", "--preset=aeneas", "--sysroot=default",
                    "--consts=values", "--remove-adt-clauses", "--lift-associated-types=*",
                    "--remove-unused-clauses"]
                for name in ["zakura_udon", "core::cmp::*::is_lt", "core::num::*::unsigned_abs",
                             "core::num::*::wrapping_neg", "core::num::*::wrapping_abs", "core::num::*::is_negative"]:
                    command.extend(["--include", name])
                for method in opaque:
                    command.extend(["--opaque", method_prefix + method])
                for root in roots:
                    command.extend(["--start-from", root])
                command.extend(["--no-dedup-serialized-ast", "--rustc-arg=-Coverflow-checks=on",
                    "--rustc-arg=-Cdebug-assertions=on", "--dest-file", str(raw), "--", "--lib",
                    "--locked", *(["--offline"] if args.offline else [])])
                run(label + "-charon", ["/bin/zsh", "-c", 'ulimit -s 65520\nexec "$@"',
                    "charon-main-stack", *command], large)
                data = json.loads(raw.read_text())
                if data["has_errors"]:
                    raise RuntimeError("Charon exported a partial " + namespace + " model")
                check_ordering(data)
                previous = raw
                for name in adapters:
                    adapted = output / "llbc" / (label + "-" + name + ".llbc")
                    flags = ["--retain-callback-functions", "--large-sqrt"] if name == "project_parameters" else []
                    run(label + "-" + name, ["python3", str(HERE / "adapters" / (name + ".py")),
                        str(previous), str(adapted), *flags], output)
                    previous = adapted
                run(label + "-aeneas", [str(tools / "aeneas"), "-backend", "lean", "-namespace", namespace,
                    "-subdir", namespace, "-filter-trait-methods", "-split-files", "-no-progress-bar",
                    "-abort-on-error", *(["-max-recdepth", "16384"] if namespace == "LargeAlgorithms" else []),
                    "-dest", str(lean), str(previous)], output)
                template = lean / namespace / "FunsExternal_Template.lean"
                actual = set(re.findall(r"\baxiom\s+([A-Za-z0-9_.]+)", template.read_text()))
                if actual != expected:
                    raise RuntimeError("Unexpected large-table external models: " + repr(actual))
                if (lean / namespace / "TypesExternal_Template.lean").exists():
                    raise RuntimeError("Unexpected large-table external types: " + namespace)
                shutil.copyfile(HERE / support / "FunsExternal.lean", lean / namespace / "FunsExternal.lean")
                template.unlink()
                model_modules.extend([namespace + ".Types", namespace + ".FunsExternal", namespace + ".Funs"])
        if CATALOG.get("signed62_helper_roots"):
            roots = CATALOG["signed62_helper_roots"]
            if roots != ["to_signed62", "pack62", "unpack62", "negative_eta_multiplier"]:
                raise RuntimeError("Unexpected signed-62 helper extraction scope")
            raw = output / "llbc/signed62-helpers.llbc"
            command = [str(tools / "charon"), "cargo", "--preset=aeneas", "--sysroot=default",
                "--include", "zakura_udon", "--remove-adt-clauses", "--lift-associated-types=*"]
            for root in roots:
                command.extend(["--start-from", "zakura_udon::field::pasta::safegcd::" + root])
            command.extend(["--no-dedup-serialized-ast", "--rustc-arg=-Coverflow-checks=on",
                "--rustc-arg=-Cdebug-assertions=on", "--dest-file", str(raw), "--", "--package",
                "zakura-udon", "--lib", "--locked", *(["--offline"] if args.offline else [])])
            run("signed62-charon", ["/bin/zsh", "-c", 'ulimit -s 65520\nexec "$@"',
                "charon-main-stack", *command], repo)
            data = json.loads(raw.read_text())
            if data["has_errors"]:
                raise RuntimeError("Charon exported a partial signed-62 helper model")
            targets = [item["key"] for item in data["translated"]["target_information"]]
            if targets != ["aarch64-apple-darwin"]:
                raise RuntimeError("The cancellation helper requires the pinned AArch64 target")
            run("signed62-aeneas", [str(tools / "aeneas"), "-backend", "lean", "-namespace", "Signed62Native",
                "-subdir", "Signed62Native", "-split-files", "-no-progress-bar", "-abort-on-error",
                "-dest", str(lean), str(raw)], output)
            files = {item.name for item in (lean / "Signed62Native").iterdir()}
            if files != {"Types.lean", "Funs.lean"}:
                raise RuntimeError("Unexpected signed-62 external models: " + repr(files))
            model_modules.extend(["Signed62Native.Types", "Signed62Native.Funs"])
        if CATALOG.get("comba_helper_roots"):
            roots = CATALOG["comba_helper_roots"]
            if roots != ["add_product", "start_column", "start_columns", "merge_columns"]:
                raise RuntimeError("Unexpected Comba helper extraction scope")
            raw = output / "llbc/comba-helpers.llbc"
            command = [str(tools / "charon"), "cargo", "--preset=aeneas", "--sysroot=default",
                "--include", "zakura_udon", "--remove-adt-clauses", "--lift-associated-types=*"]
            for root in roots:
                command.extend(["--start-from", "zakura_udon::field::pasta::products::" + root])
            command.extend(["--no-dedup-serialized-ast", "--rustc-arg=-Coverflow-checks=on",
                "--rustc-arg=-Cdebug-assertions=on", "--dest-file", str(raw), "--", "--package",
                "zakura-udon", "--lib", "--locked", *(["--offline"] if args.offline else [])])
            run("comba-charon", ["/bin/zsh", "-c", 'ulimit -s 65520\nexec "$@"',
                "charon-main-stack", *command], repo)
            data = json.loads(raw.read_text())
            if data["has_errors"]:
                raise RuntimeError("Charon exported a partial Comba helper model")
            targets = [item["key"] for item in data["translated"]["target_information"]]
            if targets != ["aarch64-apple-darwin"]:
                raise RuntimeError("The Comba helpers require the pinned AArch64 target")
            run("comba-aeneas", [str(tools / "aeneas"), "-backend", "lean", "-namespace", "CommonComba",
                "-subdir", "CommonComba", "-split-files", "-no-progress-bar", "-abort-on-error",
                "-dest", str(lean), str(raw)], output)
            expected = {
                "TypesExternal_Template.lean": {"core.array.iter.IntoIter"},
                "FunsExternal_Template.lean": {
                    "Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter",
                    "core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next"},
            }
            files = {item.name for item in (lean / "CommonComba").iterdir()}
            if files != {"Types.lean", "Funs.lean", *expected}:
                raise RuntimeError("Unexpected Comba model files: " + repr(files))
            for name, declarations in expected.items():
                template = lean / "CommonComba" / name
                external = set(re.findall(r"\baxiom\s+([A-Za-z0-9_.]+)", template.read_text()))
                if external != declarations:
                    raise RuntimeError("Unexpected Comba external models: " + name)
                destination = name.replace("_Template", "")
                shutil.copyfile(HERE / "comba_support" / destination,
                                lean / "CommonComba" / destination)
                template.unlink()
            model_modules.extend(["CommonComba.TypesExternal", "CommonComba.Types",
                                  "CommonComba.FunsExternal", "CommonComba.Funs"])
        for module in CATALOG["modules"]:
            shutil.copyfile(HERE / "proofs" / (module + ".lean"), lean / (module + ".lean"))
        for source in lean.rglob("*.lean"):
            if re.search(r"\b(sorry|admit|axiom|opaque|native_decide)\b", source.read_text()):
                raise RuntimeError("Unexpected proof/model hole in " + str(source))
        shutil.copyfile(backend / "lean-toolchain", lean / "lean-toolchain")
        (lean / "lakefile.lean").write_text(
            "import Lake\nopen Lake DSL\nrequire aeneas from " + json.dumps(str(backend)) +
            "\npackage commonArithmetic\n" + "".join(
                "@[default_target] lean_lib " + module + "\n" for module in CATALOG["modules"]))
        (lean / ".lake").mkdir()
        (lean / ".lake/packages").symlink_to(backend / ".lake/packages", target_is_directory=True)
        result["model_hashes"] = {str(p.relative_to(lean)): digest(p)
                                  for p in sorted(lean.rglob("*.lean")) if p.parent != lean}
        result["proof_source_hashes"] = {m: digest(lean / (m + ".lean")) for m in CATALOG["modules"]}
        if args.prepare_only:
            result["status"] = "prepared"
            save()
            return
        for module in [*model_modules, *CATALOG["modules"]]:
            relative = module.replace(".", "/")
            olean = lean / ".lake/build/lib/lean" / (relative + ".olean")
            olean.parent.mkdir(parents=True, exist_ok=True)
            run("lean-" + module, ["lake", "env", "lean", "-j2", relative + ".lean",
                                   "-o", str(olean)], lean)
        census_modules = [CATALOG["census_module"]] if "census_module" in CATALOG \
            else CATALOG["modules"]
        census = "\n".join((output / "logs" / ("lean-" + m + ".log")).read_text()
                           for m in census_modules)
        check_proof_census(census, CATALOG)
        (output / "logs/census.log").write_text(census)
        result.update(status="passed", proofs_checked=True, proved=CATALOG["proved"],
                      theorem_count=len(CATALOG["proved"]))
        save()
        print(f"Checked {len(CATALOG['proved'])} declarations and their axiom census.")
    except Exception:
        result["status"] = "failed"
        save()
        raise


if __name__ == "__main__":
    main()
