# Third-party notices

This crate is an Apache-2.0 derivative of the projects listed below. Retained
Supranational source files preserve their copyright and license headers and
carry a prominent Zakura modification notice. The Zcash-derived GLV header
carries separate Electric Coin Company attribution.

- **Semolina 0.1.4**, commit
  `13ffc78074a6fbec44a4fd12b7f585a0bc1dc154`: Pasta field arithmetic,
  constants, assembly generators, and generated CPU assembly.
- **Sppark**, commit
  `17278d74295392f9813f009300b257a688422b7a`: affine and XYZZ group formulas
  and the base Pippenger structure. Zakura removed all GPU and native-pool
  paths and added serial signed-Booth recoding.
- **pasta-msm**, commit
  `861357baceec7690a3a85631a9d5eba9f08076ed`: the typed Pallas/Vesta wrapper
  and native bridge structure. Zakura replaced the bridge with two
  status-returning, exception-contained entrypoints.
- **Zcash pasta_curves**, commit
  `f76fecb533003e525160e7e6d299b955a9d78cc4`: the Pasta GLV short-basis and
  Babai-rounding constants, checked decomposition design, endomorphism, and
  boundary-test witnesses. Zakura selected its Apache-2.0 license option and
  adapted the implementation to the private caller-thread native backend.

Each upstream component is used under Apache License 2.0. None of these
upstream revisions contains a `NOTICE` file. The complete license text is in
[`LICENSE-APACHE`](LICENSE-APACHE).

The crate depends on the workspace's `pasta_curves` crate under its
MIT-or-Apache-2.0 license; no `pasta_curves` source is copied here.
