# SLH-DSA-SHA2-192s reference vectors

These files contain public test material, never wallet secrets.

`sha2_192s_nist.seed` and `sha2_192s_nist.pk` are from NIST ACVP
[keyGen internalProjection.json, group 5, case 41](https://github.com/usnistgov/ACVP-Server/blob/112690e8484dba7077709a05b1f3af58ddefdd5d/gen-val/json-files/SLH-DSA-keyGen-FIPS205/internalProjection.json).
The parameter set is SLH-DSA-SHA2-192s. The 72-byte seed concatenates `skSeed`,
`skPrf`, and `pkSeed` in that order; the 48-byte public key is the published `pk`.

`sha2_192s_openssl.sig` was independently generated and verified with OpenSSL
4.0.3 using that NIST key, a message of 32 bytes of `0x2a`, context
`common/slh-dsa/test`, and deterministic Pure SLH-DSA. The context is only for
this test and does not specify a protocol context. OpenSSL key generation also
reproduced the published NIST public key.

To reproduce the signature with OpenSSL 3.5 or newer, from this directory:

```python
import subprocess
import tempfile
from pathlib import Path

seed = Path("sha2_192s_nist.seed").read_bytes()
with tempfile.TemporaryDirectory() as directory:
    key = Path(directory) / "test-key.pem"
    message = Path(directory) / "message.bin"
    signature = Path(directory) / "signature.bin"
    message.write_bytes(bytes([42]) * 32)
    subprocess.run([
        "openssl", "genpkey", "-algorithm", "SLH-DSA-SHA2-192s",
        "-pkeyopt", "hexseed:" + seed.hex(), "-out", str(key),
    ], check=True)
    subprocess.run([
        "openssl", "pkeyutl", "-sign", "-rawin", "-inkey", str(key),
        "-in", str(message), "-out", str(signature),
        "-pkeyopt", "context-string:common/slh-dsa/test",
        "-pkeyopt", "deterministic:1",
    ], check=True)
    assert signature.read_bytes() == Path("sha2_192s_openssl.sig").read_bytes()
```

The Rust tests compare the generated public key and entire signature to these
fixtures, then verify the independent signature. Tests use the bundled fixtures
and need neither OpenSSL nor network access.
