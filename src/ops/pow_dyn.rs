use crate::*;

/// Exponentiation with optional runtime context.
///
/// This operation raise its first operand to the second
/// and return a value of the type of the formar, optionally
/// taking an extra parameter that describes the
/// underlying algebraic structure at runtime.
///
/// The operation must not fail in any case.
///
/// The default implementation is usually reasonably performant.
pub trait PowDyn<C, D, Rhs: ClosedAddDyn<D> + ClosedSubDyn<D> + ZeroDyn<D> + OneDyn<D> + EuclidDyn<D>>:
    Sized + Clone + ClosedMulDyn<C> + OneDyn<C> + PowCostDyn<C, D, Rhs>
{
    /// Computes `self ^ rhs`. [Read more][PowDyn]
    fn pow_d(&self, rhs: &Rhs, ctx: &C, ctx2: &D) -> Self {
        if rhs.is_zero_d(ctx2) {
            return Self::one_d(ctx);
        }
        if rhs.is_one_d(ctx2) {
            // this check serves in case 1 + 1 == 0 under Rhs
            return self.clone();
        }
        let two = Rhs::one_d(ctx2).add_d(&Rhs::one_d(ctx2), ctx2);
        let (q, r) = rhs.euclid_div_rem_d(&two, ctx2);
        let mut x = self.pow_d(&q, ctx, ctx2);
        x = x.mul_d(&x, ctx);
        if r.is_one_d(ctx2) {
            x.mul_assign_d(self, ctx);
        }
        x
    }
}

/// Expected cost of operation.
///
/// This is necessary for runtime algorithm selection.
pub trait PowCostDyn<C, D, Rhs: ClosedAddDyn<D> + ClosedSubDyn<D> + ZeroDyn<D> + OneDyn<D> + EuclidDyn<D> + EuclidCostDyn<D>>: ClosedMulCostDyn<C> {
    /// Estimates the cost of raising a value to another, in arbitrary units of time.
    fn pow_cost_d(ctx: &C, ctx2: &D) -> f64 {
        let mut x = Rhs::zero_d(ctx2).sub_d(&Rhs::one_d(ctx2), ctx2);
        let two = Rhs::one_d(ctx2).add_d(&Rhs::one_d(ctx2), ctx2);
        let mut iterations = 0.0;
        while !x.is_zero_d(ctx2) {
            iterations += 1.0;
            x = x.euclid_div_d(&two, ctx2);
        }
        (iterations - 1.0) * (Rhs::euclid_cost_d(ctx2) + 1.5 * Self::mul_cost_d(ctx))
    }
}
