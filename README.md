# cralgebra
A fast crypto algebra library.

## Status
The current version is to be considered _unstable_, and breaking changes are possible.
New features and fixes will be added in small incremental releases.

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

"Complete" optimization here refers to using optimal algorithms.
SIMD and/or inline assembly may also be considered in the future.

## Using the API
See the [documentation](https://docs.rs/cralgebra/latest).

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
