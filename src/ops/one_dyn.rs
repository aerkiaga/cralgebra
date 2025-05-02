/// Multiplicative identity element.
///
/// The value returned by this operation must leave an operand
/// unchanged when multiplied with it.
/// Optionally, it can take an extra parameter that describes the
/// underlying algebraic structure at runtime.
pub trait OneDyn<C>: Sized + Eq {
    /// Returns the multiplicative identity, `1`. [Read more][OneDyn]
    fn one_d(ctx: &C) -> Self;

    /// Checks whether a value matches `1`. [Read more][OneDyn]
    fn is_one_d(&self, ctx: &C) -> bool {
        self == &Self::one_d(ctx)
    }
}
