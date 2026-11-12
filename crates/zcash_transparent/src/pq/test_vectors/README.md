# SLH-DSA-SHA2 reference vectors

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

## SHA2-128f references

`sha2_128f_nist.seed` and `sha2_128f_nist.pk` use the same pinned NIST
key-generation source above, group 3, case 21 (SLH-DSA-SHA2-128f). Its
48-byte seed is `skSeed || skPrf || pkSeed`; its public key is 32 bytes.
The source JSON SHA-256 is
`d7c53a1b6450087047b57aae83a5a51a0ac89ecdb23ebe071e83fbb69ae9d920`.

`sha2_128f_openssl.sig` was generated using the same message, context and
deterministic Pure interface as the 192s fixture, with OpenSSL 4.0.3 and
`SLH-DSA-SHA2-128f`. It is 17,088 bytes, with SHA-256
`02066fd92ecbc2c18251f36056051e50b74366cc93ee52ba8a73cb3127aa1ac7`.
An independent in-memory OpenSSL run reproduced this signature hash. To
reproduce it, substitute the 128f fixture names and algorithm in the
commands above. These are public test vectors, never wallet secrets.
