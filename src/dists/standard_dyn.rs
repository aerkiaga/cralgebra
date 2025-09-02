/// Uniform random distribution with optional parameter.
pub struct StandardDyn<'a, C> {
    pub ctx: &'a C,
}

impl<'a, C> StandardDyn<'a, C> {
    /// Creates a new distribution object.
    pub fn new(ctx: &'a C) -> Self {
        Self { ctx }
    }
}
