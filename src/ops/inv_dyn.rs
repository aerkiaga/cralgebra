/// Multiplicative inverse with optional runtime context.
///
/// This operation must take an input value and return a
/// value of the same type that gives [OneDyn::one_d]
/// when multiplied with the input, optionally
/// taking an extra parameter that describes the
/// underlying algebraic structure at runtime.
pub trait InvDyn<C>: Sized {
    /// Computes `inv` so that `self * inv = 1`. [Read more][InvDyn]
    fn inv_d(&self, ctx: &C) -> Self;
}
