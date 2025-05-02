//! Traits defining operations.

mod cyclic_ord_dyn;
pub use cyclic_ord_dyn::*;
mod cyclic_ord_zero_dyn;
pub use cyclic_ord_zero_dyn::*;

mod closed_add_dyn;
pub use closed_add_dyn::*;
mod closed_sub_dyn;
pub use closed_sub_dyn::*;
mod zero_dyn;
pub use zero_dyn::*;

mod closed_mul_dyn;
pub use closed_mul_dyn::*;
mod centered_mul_dyn;
pub use centered_mul_dyn::*;
mod outer_mul_dyn;
pub use outer_mul_dyn::*;
mod one_dyn;
pub use one_dyn::*;

mod pow_dyn;
pub use pow_dyn::*;
mod inv_dyn;
pub use inv_dyn::*;

mod euclid_dyn;
pub use euclid_dyn::*;
mod order_dyn;
pub use order_dyn::*;
