use crate::*;

/// Centered modular multiplication with optional runtime context.
///
/// This operation must multiply two values of the same type
/// and return a value of that type equal to their product
/// divided by a modulo. It optionally takes
/// an extra parameter that describes the
/// underlying algebraic structure at runtime.
///
/// The operation must not fail in any case.
pub trait CenteredMulDyn<C>: ClosedMulDyn<C> + CenteredMulCostDyn<C> {
    /// Computes `self * rhs / m`. [Read more][CenteredMulDyn]
    fn centered_mul_d(&self, rhs: &Self, ctx: &C) -> Self;

    /// Computes `(self * rhs / m, self * rhs % m)`. [Read more][ClosedMulDyn]
    fn widening_mul_d(&self, rhs: &Self, ctx: &C) -> (Self, Self) {
        (self.mul_d(rhs, ctx), self.centered_mul_d(rhs, ctx))
    }
}

/// Expected cost of operation.
///
/// This is necessary for runtime algorithm selection.
pub trait CenteredMulCostDyn<C>: ClosedMulCostDyn<C> {
    /// Estimates the cost of centered multiplication of two values, in arbitrary units of time.
    fn centered_mul_cost_d(ctx: &C) -> f64 {
        Self::mul_cost_d(ctx)
    }
}
