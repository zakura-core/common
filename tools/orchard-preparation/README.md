# Orchard arithmetic compatibility controls

The control revision is `80d39d9b1c41ce6c21c87f53c42deb317ce06e84`. The exporter
builds its Pasta and Poseidon implementations in an isolated archive. Expected
bytes are generated independently of Udon.

```sh
python3 tools/orchard-preparation/export.py tools/orchard-preparation/fixtures
```

The [fixture manifest](fixtures/manifest.json) pins SHA-256 digests, the source
revision, and the RNG seed. Records contain canonical encodings, without native
field representations:

| File | Record layout |
| --- | --- |
| `poseidon-fp.bin`, `poseidon-fq.bin` | 192 round constants, 9 MDS entries, then five `(left, right, hash)` triples; each field is 32-byte little endian |
| `key-agreement.bin` | 132 `(scalar, compressed base, compressed product)` triples, including zero, one, minus one, and identity |

Review fixture changes against the pinned reference implementation; generating
expected bytes from the candidate would hide a shared regression.

## Paired arithmetic measurements

Build once, then run timing separately from builds and tests:

```sh
python3 tools/orchard-preparation/bench.py /tmp/orchard-arithmetic --build-only
python3 tools/orchard-preparation/bench.py /tmp/orchard-arithmetic --measure-only --control-control
python3 tools/orchard-preparation/bench.py /tmp/orchard-arithmetic --measure-only
```

The arithmetic consumer uses identical canonical inputs and 16 scalar schedules,
one worker, and matched default field backends. It measures borrowed retained
tables, table preparation, preparation plus consumption, and projective
multiplication through affine output. Required API allocations remain inside
timing; reusable caller scratch and retained tables are prepared outside it.
Each block runs ABBA. Control/control runs establish noise before judging
candidate/control ratios.

The [ARM64 arithmetic samples](results/2026-10-11-arm64/arithmetic) retain raw
CSV runs, summaries, and binary, fixture, and source hashes. Those hashes identify
the captured build, including its documentation; they are not checksums of the
current working tree. Raw samples remain immutable evidence of the recorded run.
