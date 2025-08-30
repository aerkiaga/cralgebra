use crate::*;

/// Euclidean division with optional runtime context.
///
/// Takes two elements `self` and `rhs` of the same type,
/// and returns values satisfying `self = q * rhs + r",
/// where, given some ordering, `r < rhs`.
pub trait EuclidDyn<C>: Sized + ClosedMulDyn<C> + ClosedAddDyn<C> {
    /// Computes `q` so that `self = q * rhs + r`.
    fn euclid_div_d(&self, rhs: &Self, ctx: &C) -> Self;

    /// Computes `r` so that `self = q * rhs + r`.
    fn euclid_rem_d(&self, rhs: &Self, ctx: &C) -> Self;

    /// Computes `(q, r)` so that `self = q * rhs + r`.
    fn euclid_div_rem_d(&self, rhs: &Self, ctx: &C) -> (Self, Self) {
        (self.euclid_div_d(rhs, ctx), self.euclid_rem_d(rhs, ctx))
    }
}
