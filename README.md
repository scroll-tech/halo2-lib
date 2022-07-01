# Halo2 Pairing

## Instruction

Using privacy-scaling-exploration/halo2 requires rust nightly build. Install it using

```
rustup install nightly
```

Compile the repo

```
cargo +nightly build
```

Run examples

```
cargo +nightly test -- --nocapture test_example1
cargo +nightly test -- --nocapture test_example2
```

Plot the circuit layout

```
cargo +nightly test --all-features -- --nocapture plot_example1
cargo +nightly test --all-features -- --nocapture plot_example2
```
