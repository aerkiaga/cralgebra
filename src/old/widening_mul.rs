pub trait WideningMul: Sized {
    fn wdmul(&self, other: &Self) -> (Self, Self);
}

impl WideningMul for u8 {
    fn wdmul(&self, other: &Self) -> (Self, Self) {
        self.widening_mul(*other)
    }
}

impl WideningMul for u16 {
    fn wdmul(&self, other: &Self) -> (Self, Self) {
        self.widening_mul(*other)
    }
}

impl WideningMul for u32 {
    fn wdmul(&self, other: &Self) -> (Self, Self) {
        self.widening_mul(*other)
    }
}

impl WideningMul for u64 {
    fn wdmul(&self, other: &Self) -> (Self, Self) {
        self.widening_mul(*other)
    }
}

impl WideningMul for u128 {
    fn wdmul(&self, other: &Self) -> (Self, Self) {
        self.widening_mul(*other)
    }
}
