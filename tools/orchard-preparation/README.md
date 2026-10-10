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
