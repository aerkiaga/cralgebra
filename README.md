# cralgebra
A fast crypto algebra library.

## Status

- ✅: complete
- ⚡: partial
- ❌: none

| Feature | Completion | Optimization |
|---------|------------|--------------|
| Modular arithmetic | ✅ | ✅ |
| Big integers | ⚡ | ❌ |
| Cyclotomic polynomials | ⚡ | ❌ |
| Primality testing | ⚡ | ⚡ |
| Uniform sampling | ⚡ | ✅ |
| Discrete Gaussian sampling | ⚡ | ✅ |

## Using the API

## Performance
Run this to measure latencies for different operations:

```shell
cargo run --example bench --release
```

This `Cargo.toml` configuration is recommended for maximum performance:

```toml
[profile.release]
opt-level = 3
debug-assertions = false
overflow-checks = false
lto = true
panic = 'unwind'
incremental = false
codegen-units = 1
rpath = false
```

Further tips:

- Use the most specific type or method for each task.
- Use `MontgomeryDyn` instead of `ModularDyn` if doing multiple operations in series, containing multiplications.

## Alternative projects
- [feanor-math](https://github.com/FeanorTheElf/feanor-math): more featured, with a different approach to API organization.
