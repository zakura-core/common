# Native SLH-DSA reference fixtures

These are public test seeds and signatures, not wallet secrets.

The key-generation fixtures come from the pinned NIST ACVP
[keyGen internalProjection.json](https://github.com/usnistgov/ACVP-Server/blob/112690e8484dba7077709a05b1f3af58ddefdd5d/gen-val/json-files/SLH-DSA-keyGen-FIPS205/internalProjection.json).
SHA2-128f uses group 3, case 21; SHA2-192s uses group 5, case 41.
Each `.seed` is `skSeed || skPrf || pkSeed`; `.pk` is the published public key.
The source JSON SHA-256 is `d7c53a1b6450087047b57aae83a5a51a0ac89ecdb23ebe071e83fbb69ae9d920`.

The `.sig` files were generated with OpenSSL 4.0.3, deterministic Pure SLH-DSA,
a message of 32 bytes of `0x2a`, and context `common/native-slh/vector`.
This fixture context is distinct from the native transaction-signing contexts.

To reproduce, run `openssl genpkey -algorithm SLH-DSA-SHA2-128f -pkeyopt hexseed:<seed hex> -out <temporary key>`;
then `openssl pkeyutl -sign -rawin -inkey <temporary key> -in <message> -out <signature> -pkeyopt context-string:common/native-slh/vector -pkeyopt deterministic:1`.
Use `SLH-DSA-SHA2-192s` and its seed for the other fixture. Remove temporary keys afterwards.

Signature SHA-256 values:

* `128f.sig`: `4a30d1b200c7738a6247ee70b50c60e9a69cc43dcfc142bed580052cef651a46`
* `192s.sig`: `bccd4949f87b725ba12278605b19772d019d8a8f89a5b796f2e3fa68d5a12d66`

Tests compare the entire public key and signature, then exercise verification and rejection.
