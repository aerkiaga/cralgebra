/// Closed addition with optional runtime context.
///
/// This operation must add two values of the same type
/// and return a value of that type, optionally
/// taking an extra parameter that describes the
/// underlying algebraic structure at runtime.
///
/// The operation must not fail in any case.
pub trait ClosedAddDyn<C>: Sized + ClosedAddCostDyn<C> {
    /// Computes `self + rhs`. [Read more][ClosedAddDyn]
    fn add_d(&self, rhs: &Self, ctx: &C) -> Self;

    /// Computes `self + rhs` and assigns the result to `self`. [Read more][ClosedAddDyn]
    fn add_assign_d(&mut self, rhs: &Self, ctx: &C) {
        *self = self.add_d(rhs, ctx);
    }
}

/// Expected cost of operation.
///
/// This is necessary for runtime algorithm selection.
pub trait ClosedAddCostDyn<C> {
    /// Estimates the cost of adding two values, in arbitrary units of time.
    fn add_cost_d(ctx: &C) -> f64;
}
