use crate::*;

/// The polynomial ring `T[x]/(x^N + 1)`.
///
/// This is only a cyclotomic field if `N`
/// is a power of two. Otherwise, it is simply
/// a ring, and division, inverses, etc. will
/// produce an error in debug mode.
pub struct Cyclotomic<const N: usize, T> {
    pub coefficients: [T; N],
}

impl<const N: usize, C, T: ClosedAddDyn<C>> ClosedAddDyn<C> for Cyclotomic<N, T> {
    fn add_d(&self, rhs: &Self, ctx: &C) -> Self {
        Self {
            coefficients: std::array::from_fn(|i| {
                self.coefficients[i].add_d(&rhs.coefficients[i], ctx)
            }),
        }
    }
}

impl<C, const N: usize, T: ClosedAddCostDyn<C>> ClosedAddCostDyn<C> for Cyclotomic<N, T> {
    fn add_cost_d(ctx: &C) -> f64 {
        N as f64 * T::add_cost_d(ctx)
    }
}
