# Fixtures

All fixtures are public chain data, hex encoded.

`blocks/block-{main,test}-<height>.txt` are raw blocks copied unchanged from
Zakura's `crates/zakura-test/src/vectors` (commit
`ab45d303b4ceeb7c6ac5c9dabd5fa23de9c729eb`), where each was fetched with
`zcash-cli [-testnet] getblock <height> 0`. They were chosen to cover v1 to v5
on both networks, Sprout (PHGR13 and Groth16), Sapling and Orchard.

`v6/` holds two public mainnet v6 transactions with Ironwood actions, copied
from wallet-pir's test fixtures (commit
`f3539afa562b5bb74debdc2fc0179250f7571497`):

- `main-3483367-ironwood-f337d967.hex`: transaction
  `f337d9675817668120ae626021f61e5350ff5412beeb5e42b67bd412452b8d13`, block
  height 3483367, fetched from a Zakura archive node's RPC. Two Ironwood
  actions, no other pool; Ironwood value balance 10000, expiry height 3483371
  (as reported by the RPC).
- `main-3496114-ironwood-2060cf68.hex`: transaction
  `2060cf68088b55dcd9e2f91556c72528e1ab8c6834ea3f71b8c80fca9fc51653`, block
  height 3496114, fetched with `getrawtransaction <txid> 0`.
