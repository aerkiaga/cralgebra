# Changelog
This project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).
See also [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]
This release introduces breaking changes.

### Added
- Implementation of the non-dynamic `ClosedAdd` trait for all types supporting it.
- Documentation for the top-level crate.

### Changed
- **Breaking:** renamed every `*Context` to `*Ctx` for brevity.
- **Breaking:** renamed the `misc` module to `dists`.

### Removed
- Examples and API guidelines from `README.md`.

## [0.1.1] - 2025-09-02

### Added

- Tests for `Z2_64N` addition and multiplication.
- This `CHANGELOG.md` file.
- "Status" section in `README.md`.

### Fixed

- `Z2_64N` multiplication.
- Alternative project link in `README.md`.

### Removed

- Unused `static-toml` dependency.

## [0.1.0] - 2025-08-30

### Added

- Types `Z2_8` through `Z2_128`.
- Type `Z2_64N`, implementing addition, multiplication and random sampling.
- Types `ModularDyn` and `MontgomeryDyn`.
- Type `Cyclotomic`, implementing addition.
- Closed addition, subtraction and multiplication traits.
- Identity element, exponentiation and multiplicative inverse traits.
- Generalized and specialized multiplication traits.
- Euclidean division trait.
- Cyclic order traits.
- Standard and discrete Gaussian distributions.
- Miller-Rabin primality test.
