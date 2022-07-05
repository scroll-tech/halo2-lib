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

Run main

```
cargo +nightly test -- --nocapture test_gates
```

Plot the circuit layout

```
cargo +nightly test --all-features -- --nocapture plot_gates
```
