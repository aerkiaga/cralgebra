/// Closed addition with optional runtime context.
///
/// This operation must add two values of the same type
/// and return a value of that type, optionally
/// taking an extra parameter that describes the
/// underlying algebraic structure at runtime.
///
/// The operation must not fail in any case.
pub trait ClosedAddDyn<C>: Sized {
    /// Computes `self + rhs`. [Read more][ClosedAddDyn]
    fn add_d(&self, rhs: &Self, ctx: &C) -> Self;

    /// Computes `self + rhs` and assigns the result to `self`. [Read more][ClosedAddDyn]
    fn add_assign_d(&mut self, rhs: &Self, ctx: &C) {
        *self = self.add_d(rhs, ctx);
    }
}

/// Closed addition.
///
/// This operation must add two values of the same type
/// and return a value of that type.
///
/// The operation must not fail in any case.
pub trait ClosedAdd: ClosedAddDyn<()> {
    /// Computes `self + rhs`. [Read more][ClosedAdd]
    fn add(&self, rhs: &Self) -> Self {
        self.add_d(rhs, &())
    }

    /// Computes `self + rhs` and assigns the result to `self`. [Read more][ClosedAdd]
    fn add_assign(&mut self, rhs: &Self) {
        self.add_assign_d(rhs, &())
    }
}
