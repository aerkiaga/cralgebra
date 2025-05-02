/// Additive identity element.
///
/// The value returned by this operation must leave an operand
/// unchanged when added to it.
/// Optionally, it can take an extra parameter that describes the
/// underlying algebraic structure at runtime.
pub trait ZeroDyn<C>: Sized + Eq {
    /// Returns the additive identity, `0`. [Read more][ZeroDyn]
    fn zero_d(ctx: &C) -> Self;

    /// Checks whether a value matches `0`. [Read more][ZeroDyn]
    fn is_zero_d(&self, ctx: &C) -> bool {
        self == &Self::zero_d(ctx)
    }
}
