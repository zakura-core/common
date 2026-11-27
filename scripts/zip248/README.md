# ZIP 248 vector oracle

`oracle.py` is an independent implementation of the ZIP 248 v7 transaction
identifier, authorizing data commitment, and variant 0 signature digests,
written from the ZIP text alone. It checks the frozen vectors in
`crates/zcash_primitives/src/transaction/v7/tests/vectors.rs`, which
`scripts/tests/test_zip248_vectors.py` runs with the other script tests:

```sh
python3 scripts/zip248/oracle.py crates/zcash_primitives/src/transaction/v7/tests/vectors.rs \
    crates/zcash_primitives/src/transaction/v7/tests/envelope_vectors.rs
```

The second file is optional. Its envelope vectors edit frozen vectors so that the typed
layer rejects them while their txid and authorizing data commitment stay defined, and
the oracle checks only those two digests for them, accepting any `sighashInfo`. The
Rust test `envelope_digests_match_the_oracle_where_typed_decoding_fails` applies each
edit again and checks that it reproduces the frozen bytes. To compute the digests of a
new envelope vector, pass its transaction bytes in hex:

```sh
python3 scripts/zip248/oracle.py --envelope-digests <transaction hex>
```

To regenerate the vectors, dump them from the Rust generator, then check and
format the dump:

```sh
V7_VECTOR_DUMP=/tmp/v7_vectors.txt cargo test -p zakura-primitives --lib \
    --features transparent-inputs,test-dependencies -- --ignored dump_vectors_for_oracle
python3 scripts/zip248/oracle.py /tmp/v7_vectors.txt
python3 scripts/zip248/format_vectors.py /tmp/v7_vectors.txt \
    crates/zcash_primitives/src/transaction/v7/tests/vectors.rs
cargo fmt --all
```
