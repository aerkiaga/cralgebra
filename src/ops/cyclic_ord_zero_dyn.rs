use crate::*;

/// Special case of cyclic order with a closed, zero lower bound.
///
/// Equivalent to [CyclicOrdDyn] with the lower bound set to
/// [ZeroDyn::zero_d] plus a check against it. The default implementation can be
/// overridden for efficiency.
pub trait CyclicOrdZeroDyn<C>:
    Sized + CyclicOrdDyn<C> + ZeroDyn<C> + CyclicOrdZeroCostDyn<C>
{
    /// Returns whether `[0, self, high]` or `self == 0` for a cyclic order,
    /// equivalent to `self < high` for a linear order. [Read more][CyclicOrdZeroDyn]
    fn cyclic_lt0_d(&self, high: &Self, ctx: &C) -> bool {
        self.cyclic_lt_d(&Self::zero_d(ctx), high, ctx) || self.is_zero_d(ctx)
    }
}

/// Expected cost of operation.
///
/// This is necessary for runtime algorithm selection.
pub trait CyclicOrdZeroCostDyn<C>: CyclicOrdCostDyn<C> {
    /// Estimates the cost of checking for cyclic ordering, in arbitrary units of time.
    fn cyclic_lt0_cost_d(ctx: &C) -> f64 {
        Self::cyclic_lt_cost_d(ctx)
    }
}
