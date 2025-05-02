pub trait WrappingMul: Sized {
    fn wpmul(&self, other: &Self) -> Self;
}

impl WrappingMul for u8 {
    fn wpmul(&self, other: &Self) -> Self {
        self.wrapping_mul(*other)
    }
}

impl WrappingMul for u16 {
    fn wpmul(&self, other: &Self) -> Self {
        self.wrapping_mul(*other)
    }
}

impl WrappingMul for u32 {
    fn wpmul(&self, other: &Self) -> Self {
        self.wrapping_mul(*other)
    }
}

impl WrappingMul for u64 {
    fn wpmul(&self, other: &Self) -> Self {
        self.wrapping_mul(*other)
    }
}

impl WrappingMul for u128 {
    fn wpmul(&self, other: &Self) -> Self {
        self.wrapping_mul(*other)
    }
}
