/// Cyclic ordering relationship with optional runtime context.
///
/// This operation must produce a true value if and only if
/// the element is reached before the higher bound
/// when successively adding to the lower bound;
/// informally, it lies between those bounds.
/// Optionally, it can take an extra parameter that describes the
/// underlying algebraic structure at runtime.
///
/// The result must be false if the value equals any bound.
///
/// # Examples
/// ```rust
/// # use cralgebra::{types::*, ops::*};
/// let a = Z2_8 { inner: 4 };
/// let b = Z2_8 { inner: 57 };
/// let c = Z2_8 { inner: 188 };
/// assert!(b.cyclic_lt_d(&a, &c, &())); // [a, b, c]
/// assert!(c.cyclic_lt_d(&b, &a, &())); // [b, c, a]
/// assert!(a.cyclic_lt_d(&c, &b, &())); // [c, a, b]
/// assert!(!b.cyclic_lt_d(&c, &a, &())); // ¬[a, c, n]
/// assert!(!c.cyclic_lt_d(&a, &b, &())); // ¬[b, a, c]
/// assert!(!a.cyclic_lt_d(&b, &c, &())); // ¬[c, b, a]
/// assert!(!b.cyclic_lt_d(&b, &c, &())); // ¬[b, b, c]
/// assert!(!b.cyclic_lt_d(&a, &b, &())); // ¬[a, b, b]
/// ```
pub trait CyclicOrdDyn<C>: Sized {
    /// Returns whether `[low, self, high]` for a cyclic order,
    /// equivalent to `low < self < high` for a linear order. [Read more][CyclicOrdDyn]
    fn cyclic_lt_d(&self, low: &Self, high: &Self, ctx: &C) -> bool;
}
