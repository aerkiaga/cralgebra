/// Closed multiplication with optional runtime context.
///
/// This operation must multiply two values of the same type
/// and return a value of that type, optionally
/// taking an extra parameter that describes the
/// underlying algebraic structure at runtime.
///
/// The operation must not fail in any case.
pub trait ClosedMulDyn<C>: Sized + ClosedMulCostDyn<C> {
    /// Computes `self * rhs`. [Read more][ClosedMulDyn]
    fn mul_d(&self, rhs: &Self, ctx: &C) -> Self;

    /// Computes `self * rhs` and assigns the result to `self`. [Read more][ClosedMulDyn]
    fn mul_assign_d(&mut self, rhs: &Self, ctx: &C) {
        *self = self.mul_d(rhs, ctx);
    }
}

/// Expected cost of operation.
///
/// This is necessary for runtime algorithm selection.
pub trait ClosedMulCostDyn<C> {
    /// Estimates the cost of multiplying two values, in arbitrary units of time.
    fn mul_cost_d(ctx: &C) -> f64;
}
