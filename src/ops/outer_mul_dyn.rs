/// Generalized multiplication with optional runtime context.
///
/// This operation must multiply two values of different types
/// and return a value of the first's type, optionally
/// taking extra parameters that describe the
/// underlying algebraic structures at runtime.
///
/// The operation must not fail in any case.
pub trait OuterMulDyn<C, D, T>: Sized {
    /// Computes `self * rhs`. [Read more][OuterMulDyn]
    fn outer_mul_d(&self, rhs: &T, ctx: &C, ctx2: &D) -> Self;

    /// Computes `self * rhs` and assigns the result to `self`. [Read more][OuterMulDyn]
    fn outer_mul_assign_d(&mut self, rhs: &T, ctx: &C, ctx2: &D) {
        *self = self.outer_mul_d(rhs, ctx, ctx2);
    }
}
