use crate::*;
use rand::{
    Rng,
    distributions::{Distribution, Standard},
};

/// The `Z2^128` integer ring.
///
/// This corresponds to the `u128` type using wrapping arithmetic.
#[repr(transparent)]
#[derive(Clone, Eq, PartialEq)]
pub struct Z2_128 {
    pub inner: u128,
}

impl CyclicOrdDyn<()> for Z2_128 {
    fn cyclic_lt_d(&self, low: &Self, high: &Self, _ctx: &()) -> bool {
        if low.inner > high.inner {
            self.inner > low.inner && self.inner < high.inner
        } else {
            self.inner < low.inner && self.inner > high.inner
        }
    }
}

impl CyclicOrdZeroDyn<()> for Z2_128 {
    fn cyclic_lt0_d(&self, high: &Self, _ctx: &()) -> bool {
        self.inner < high.inner
    }
}

impl ClosedAddDyn<()> for Z2_128 {
    fn add_d(&self, rhs: &Self, _ctx: &()) -> Self {
        Self {
            inner: self.inner.wrapping_add(rhs.inner),
        }
    }
}

impl ClosedAdd for Z2_128 {}

impl ClosedSubDyn<()> for Z2_128 {
    fn sub_d(&self, rhs: &Self, _ctx: &()) -> Self {
        Self {
            inner: self.inner.wrapping_sub(rhs.inner),
        }
    }
}

impl ZeroDyn<()> for Z2_128 {
    fn zero_d(_ctx: &()) -> Self {
        Self { inner: 0 }
    }
}

impl ClosedMulDyn<()> for Z2_128 {
    fn mul_d(&self, rhs: &Self, _ctx: &()) -> Self {
        Self {
            inner: self.inner.wrapping_mul(rhs.inner),
        }
    }
}

impl CenteredMulDyn<()> for Z2_128 {
    fn centered_mul_d(&self, rhs: &Self, _ctx: &()) -> Self {
        self.widening_mul_d(rhs, &()).1
    }
    fn widening_mul_d(&self, rhs: &Self, _ctx: &()) -> (Self, Self) {
        let (low, high) = self.inner.widening_mul(rhs.inner);
        (Self { inner: low }, Self { inner: high })
    }
}

impl OneDyn<()> for Z2_128 {
    fn one_d(_ctx: &()) -> Self {
        Self { inner: 1 }
    }
}

impl InvDyn<()> for Z2_128 {
    fn inv_d(&self, _ctx: &()) -> Self {
        debug_assert!(self.inner & 1 != 0);
        let mut r = 1_u128;
        r = r.wrapping_mul(2_u128.wrapping_sub(r.wrapping_mul(self.inner)));
        r = r.wrapping_mul(2_u128.wrapping_sub(r.wrapping_mul(self.inner)));
        r = r.wrapping_mul(2_u128.wrapping_sub(r.wrapping_mul(self.inner)));
        r = r.wrapping_mul(2_u128.wrapping_sub(r.wrapping_mul(self.inner)));
        r = r.wrapping_mul(2_u128.wrapping_sub(r.wrapping_mul(self.inner)));
        r = r.wrapping_mul(2_u128.wrapping_sub(r.wrapping_mul(self.inner)));
        r = r.wrapping_mul(2_u128.wrapping_sub(r.wrapping_mul(self.inner)));
        Self { inner: r }
    }
}

#[test]
fn inv_test() {
    use rand::rngs::mock::StepRng;
    let mut rng = StepRng::new(0, 0x54825a7f54825a7f);
    let base_dist = StandardDyn::new(&());
    for _ in 0..100 {
        let mut a: Z2_128 = rng.sample(&base_dist);
        a.inner |= 1;
        let r = a.inv_d(&());
        let one = a.mul_d(&r, &());
        println!("{}⁻¹ = {}", a.inner, r.inner);
        assert!(one.is_one_d(&()));
    }
}

impl EuclidDyn<()> for Z2_128 {
    fn euclid_div_d(&self, rhs: &Self, _ctx: &()) -> Self {
        Self {
            inner: self.inner.div_euclid(rhs.inner),
        }
    }

    fn euclid_rem_d(&self, rhs: &Self, _ctx: &()) -> Self {
        Self {
            inner: self.inner.rem_euclid(rhs.inner),
        }
    }
}

impl<D, T: ClosedAddDyn<D> + ClosedMulDyn<D> + OneDyn<D>> OrderDyn<(), D, T> for Z2_128 {
    fn order_d(_ctx: &(), ctx2: &D) -> T {
        let mut r = T::one_d(ctx2);
        r = r.add_d(&r, ctx2);
        r = r.mul_d(&r, ctx2);
        r = r.mul_d(&r, ctx2);
        r = r.mul_d(&r, ctx2);
        r = r.mul_d(&r, ctx2);
        r = r.mul_d(&r, ctx2);
        r = r.mul_d(&r, ctx2);
        r = r.mul_d(&r, ctx2);
        r
    }
}

impl Distribution<Z2_128> for StandardDyn<'_, ()> {
    fn sample<R: ?Sized + Rng>(&self, rng: &mut R) -> Z2_128 {
        Z2_128 {
            inner: rng.sample(Standard),
        }
    }
}
