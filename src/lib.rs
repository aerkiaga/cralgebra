#![feature(bigint_helper_methods)]

//! This crate seeks to provide fast algebraic primitives for cryptography.
//!
//! # Basic usage
//! Start by having a look inside the [types] module. **cralgebra** provides various
//! algebraic types, each implementing a few traits for basic operations (module [ops]).
//! For example:
//! ```rust
//! use cralgebra::ops::ClosedAdd;
//! use cralgebra::types::Z2_8;
//! let a: Z2_8 = 17.into();
//! let b: Z2_8 = 42.into();
//! let r = a.add(&b);
//! assert_eq!(r.inner, 59);
//! ```
//!
//! # Runtime contexts
//! Items ending in `Dyn` or `_d` require a runtime context, which has a type ending
//! in `Ctx`. For example, [ModularDyn]`<T>` is used for modular arithmetic, where
//! the modulus is provided at runtime as a [ModularCtx]. Operations on
//! [ModularDyn] (e.g., [add_d][ClosedAddDyn::add_d]) take both this context and the underlying type
//! `T`'s own context. For example:
//!
//! ```rust
//! use cralgebra::ops::ClosedAddDyn;
//! use cralgebra::types::{Z2_8, ModularDyn, ModularCtx};
//! let modulus: Z2_8 = 17.into();
//! let inner_ctx = (); // Z2_8 takes no context
//! let mod_ctx = ModularCtx::new(modulus.clone(), &inner_ctx);
//! let ctx = (mod_ctx, &inner_ctx); // this is how contexts are nested
//! let a: ModularDyn<Z2_8> = ModularDyn::new_d(4.into(), &ctx);
//! let b: ModularDyn<Z2_8> = ModularDyn::new_d(15.into(), &ctx);
//! let r = a.add_d(&b, &ctx);
//! assert_eq!(r.inner.inner, 2);
//! ```

pub mod algorithms;
//pub(crate) use algorithms::*;
pub mod ops;
pub(crate) use ops::*;
pub mod types;
pub(crate) use types::*;
pub mod dists;
pub(crate) use dists::*;
