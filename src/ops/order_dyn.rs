/// Additive order representative with optional runtime context.
///
/// This operation must return a value of the desired type
/// corresponding to a representative of the additive
/// order of the input type, optionally
/// taking an extra parameter that describes the
/// underlying algebraic structure at runtime.
pub trait OrderDyn<C, D, T>: Sized {
    /// Computes the additive order of `Self`. [Read more][OrderModDyn]
    fn order_d(ctx: &C, ctx2: &D) -> T;
}
