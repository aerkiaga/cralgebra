# cralgebra
A fast crypto algebra library.

## Status

- ✅: complete
- ✍: partial
- ❌: none

| Feature | Completion | Optimization |
|---------|------------|--------------|
| Modular arithmetic | ✅ | ✅ |
| Big integers | ✍ | ❌ |
| Cyclotomic polynomials | ✍ | ❌ |
| Primality testing | ✍ | ✍ |
| Uniform sampling | ✍ | ✅ |
| Discrete Gaussian sampling | ✍ | ✅ |

## Using the API
The API is split into a few modules:

- `types`: the algebraic datatypes.
- `ops`: traits for the different operations.
- `algorithms`: useful algorithms (e.g., primality testing).
- `misc`: other things (e.g., random distributions).

Items ending in `Dyn` or `_d` require a runtime context, which has a type ending
in `Context`. For example, `ModularDyn<T>` is used for modular arithmetic, where
the modulus is provided at runtime as a `ModularContext`. Operations on
`ModularDyn` (e.g., `add_d`) take both this context and the underlying type
`T`'s own context. For example:

```rust
let modulus: Z2_8 = 17.into();
let inner_ctx = (); // Z2_8 takes no context
let mod_ctx = ModularContext::new(modulus.clone(), &inner_ctx);
let ctx = (mod_ctx, &inner_ctx); // this is how contexts are nested
let a: ModularDyn<Z2_8> = ModularDyn::new_d(4.into(), &ctx);
let b: ModularDyn<Z2_8> = ModularDyn::new_d(15.into(), &ctx);
let r = a.add_d(&b, &ctx);
assert_eq!(r.inner.inner, 2);
```

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
