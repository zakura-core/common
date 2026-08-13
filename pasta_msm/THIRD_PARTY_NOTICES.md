# Third-party notices

This crate is an Apache-2.0 derivative of the following Supranational
projects. The retained source files preserve Supranational's copyright and
license headers and carry a prominent Zakura modification notice.

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

Each upstream project is licensed under Apache License 2.0. None of these
upstream revisions contains a `NOTICE` file. The complete license text is in
[`LICENSE-APACHE`](LICENSE-APACHE).

The crate depends on the workspace's `pasta_curves` crate under its
MIT-or-Apache-2.0 license; no `pasta_curves` source is copied here.
