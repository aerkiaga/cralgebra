use crate::*;
use rand::{
    distributions::{Distribution, Standard},
    Rng,
};

/// The `Z2^16` integer ring.
///
/// This corresponds to the `u16` type using wrapping arithmetic.
#[repr(transparent)]
#[derive(Clone, Eq, PartialEq)]
pub struct Z2_16 {
    pub inner: u16,
}

impl CyclicOrdDyn<()> for Z2_16 {
    fn cyclic_lt_d(&self, low: &Self, high: &Self, _ctx: &()) -> bool {
        if low.inner > high.inner {
            self.inner > low.inner && self.inner < high.inner
        } else {
            self.inner < low.inner && self.inner > high.inner
        }
    }
}

impl CyclicOrdCostDyn<()> for Z2_16 {
    fn cyclic_lt_cost_d(_ctx: &()) -> f64 {
        2.0 * COSTS.scale * COSTS.cmp.r_16
    }
}

impl CyclicOrdZeroDyn<()> for Z2_16 {
    fn cyclic_lt0_d(&self, high: &Self, _ctx: &()) -> bool {
        self.inner < high.inner
    }
}

impl CyclicOrdZeroCostDyn<()> for Z2_16 {
    fn cyclic_lt0_cost_d(_ctx: &()) -> f64 {
        COSTS.scale * COSTS.cmp.r_16
    }
}

impl ClosedAddDyn<()> for Z2_16 {
    fn add_d(&self, rhs: &Self, _ctx: &()) -> Self {
        Self {
            inner: self.inner.wrapping_add(rhs.inner),
        }
    }
}

impl ClosedAddCostDyn<()> for Z2_16 {
    fn add_cost_d(_ctx: &()) -> f64 {
        COSTS.scale * COSTS.add.r_16
    }
}

impl ClosedSubDyn<()> for Z2_16 {
    fn sub_d(&self, rhs: &Self, _ctx: &()) -> Self {
        Self {
            inner: self.inner.wrapping_sub(rhs.inner),
        }
    }
}

impl ClosedSubCostDyn<()> for Z2_16 {}

impl ZeroDyn<()> for Z2_16 {
    fn zero_d(_ctx: &()) -> Self {
        Self { inner: 0 }
    }
}

impl ClosedMulDyn<()> for Z2_16 {
    fn mul_d(&self, rhs: &Self, _ctx: &()) -> Self {
        Self {
            inner: self.inner.wrapping_mul(rhs.inner),
        }
    }
}

impl ClosedMulCostDyn<()> for Z2_16 {
    fn mul_cost_d(_ctx: &()) -> f64 {
        COSTS.scale * COSTS.mul.r_16
    }
}

impl CenteredMulDyn<()> for Z2_16 {
    fn centered_mul_d(&self, rhs: &Self, _ctx: &()) -> Self {
        self.widening_mul_d(rhs, &()).1
    }
    fn widening_mul_d(&self, rhs: &Self, _ctx: &()) -> (Self, Self) {
        let (low, high) = self.inner.widening_mul(rhs.inner);
        (Self { inner: low }, Self { inner: high })
    }
}

impl CenteredMulCostDyn<()> for Z2_16 {}

impl OneDyn<()> for Z2_16 {
    fn one_d(_ctx: &()) -> Self {
        Self { inner: 1 }
    }
}

impl InvDyn<()> for Z2_16 {
    fn inv_d(&self, _ctx: &()) -> Self {
        debug_assert!(self.inner & 1 != 0);
        let mut r = 1_u16;
        r = r.wrapping_mul(2_u16.wrapping_sub(r.wrapping_mul(self.inner)));
        r = r.wrapping_mul(2_u16.wrapping_sub(r.wrapping_mul(self.inner)));
        r = r.wrapping_mul(2_u16.wrapping_sub(r.wrapping_mul(self.inner)));
        r = r.wrapping_mul(2_u16.wrapping_sub(r.wrapping_mul(self.inner)));
        Self { inner: r }
    }
}

#[test]
fn inv_test() {
    use rand::rngs::mock::StepRng;
    let mut rng = StepRng::new(0, 0x54825a7f54825a7f);
    let base_dist = StandardDyn::new(&());
    for _ in 0..100 {
        let mut a: Z2_16 = rng.sample(&base_dist);
        a.inner |= 1;
        let r = a.inv_d(&());
        let one = a.mul_d(&r, &());
        println!(
            "{}⁻¹ = {}",
            a.inner, r.inner
        );
        assert!(one.is_one_d(&()));
    }
}

impl EuclidDyn<()> for Z2_16 {
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

impl EuclidCostDyn<()> for Z2_16 {
    fn euclid_cost_d(_ctx: &()) -> f64 {
        COSTS.scale * COSTS.div.r_16
    }
}

impl<D, T: ClosedAddDyn<D> + ClosedMulDyn<D> + OneDyn<D>> OrderDyn<(), D, T> for Z2_16 {
    fn order_d(_ctx: &(), ctx2: &D) -> T {
        let mut r = T::one_d(ctx2);
        r = r.add_d(&r, ctx2);
        r = r.mul_d(&r, ctx2);
        r = r.mul_d(&r, ctx2);
        r = r.mul_d(&r, ctx2);
        r = r.mul_d(&r, ctx2);
        r
    }
}

impl Distribution<Z2_16> for StandardDyn<'_, ()> {
    fn sample<R: ?Sized + Rng>(&self, rng: &mut R) -> Z2_16 {
        Z2_16 {
            inner: rng.sample(Standard),
        }
    }
}
