casemate-lib-rs
===============

The Casemate model itself.

Building it
-----------

We use `cargo` to build a statically linked archive (`libcasemate.a`)
which bundles everything, including libcore.

To do this we need to use a nightly `rustc`:

```
rustup install nightly-aarch64-unknown-linux-gnu
rustup component add rust-src --toolchain nightly
```

Then (in the casemate root), the following should be sufficient:

```
make src/lib-rs
```
