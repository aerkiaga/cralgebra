use crate::*;

/// Generalized Euclidean division with optional runtime context.
///
/// Takes two elements `self` and `rhs` of different types,
/// and returns values satisfying `self = q * rhs + r`,
/// where, given some ordering, `r < rhs`.
/// `q` and `r` shall be of the same type as `self`.
pub trait OuterEuclidDyn<C, D, T>: Sized + OuterMulDyn<C, D, T> + ClosedAddDyn<C> {
    /// Computes `q` so that `self = q * rhs + r`.
    fn outer_euclid_div_d(&self, rhs: &T, ctx: &C, ctx2: &D) -> Self;

    /// Computes `r` so that `self = q * rhs + r`.
    fn outer_euclid_rem_d(&self, rhs: &T, ctx: &C, ctx2: &D) -> Self;

    /// Computes `(q, r)` so that `self = q * rhs + r`.
    fn outer_euclid_div_rem_d(&self, rhs: &T, ctx: &C, ctx2: &D) -> (Self, Self) {
        (
            self.outer_euclid_div_d(rhs, ctx, ctx2),
            self.outer_euclid_rem_d(rhs, ctx, ctx2),
        )
    }
}
