use crate::*;

/// Closed subtraction with optional runtime context.
///
/// This operation must subtract two values of the same type
/// and return a value of that type, optionally
/// taking an extra parameter that describes the
/// underlying algebraic structure at runtime.
///
/// The operation must not fail in any case.
pub trait ClosedSubDyn<C>: Sized + ClosedAddDyn<C> {
    /// Computes `self - rhs`. [Read more][ClosedSubDyn]
    fn sub_d(&self, rhs: &Self, ctx: &C) -> Self;

    /// Computes `self - rhs` and assigns the result to `self`. [Read more][ClosedSubDyn]
    fn sub_assign_d(&mut self, rhs: &Self, ctx: &C) {
        *self = self.sub_d(rhs, ctx);
    }
}
