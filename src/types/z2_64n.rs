use crate::*;
use rand::{
    Rng,
    distributions::{Distribution, Standard},
};

/// The `Z2^64N` integer ring, for some `N`.
///
/// This corresponds to a fixed-width bigint using wrapping arithmetic.
#[derive(Clone, Eq, PartialEq)]
pub struct Z2_64N<const N: usize> {
    chunks: [u64; N],
}

impl<const N: usize> CyclicOrdDyn<()> for Z2_64N<N> {
    fn cyclic_lt_d(&self, low: &Self, high: &Self, _ctx: &()) -> bool {
        if low.cyclic_lt0_d(&high, &()) {
            low.cyclic_lt0_d(&self, &()) && self.cyclic_lt0_d(&high, &())
        } else {
            low.cyclic_lt0_d(&self, &()) || self.cyclic_lt0_d(&high, &())
        }
    }
}

impl<const N: usize> CyclicOrdZeroDyn<()> for Z2_64N<N> {
    fn cyclic_lt0_d(&self, high: &Self, _ctx: &()) -> bool {
        for n in (0..N).rev() {
            if self.chunks[n] < high.chunks[n] {
                return true;
            }
            if self.chunks[n] > high.chunks[n] {
                return false;
            }
        }
        return false;
    }
}

impl<const N: usize> LessThanDyn<()> for Z2_64N<N> {}

impl<const N: usize> ClosedAddDyn<()> for Z2_64N<N> {
    fn add_d(&self, rhs: &Self, _ctx: &()) -> Self {
        let mut carry = false;
        Self {
            chunks: std::array::from_fn(|n| {
                let r = self.chunks[n].carrying_add(rhs.chunks[n], carry);
                carry = r.1;
                r.0
            }),
        }
    }

    fn add_assign_d(&mut self, rhs: &Self, _ctx: &()) -> () {
        let mut carry = false;
        for n in 0..N {
            (self.chunks[n], carry) = self.chunks[n].carrying_add(rhs.chunks[n], carry);
        }
    }
}

impl<const N: usize> ClosedAdd for Z2_64N<N> {}

#[test]
fn add_test() {
    use rand::rngs::mock::StepRng;
    let mut rng = StepRng::new(0, 0x54825a7f54825a7f);
    let base_dist = StandardDyn::new(&());
    for _ in 0..100 {
        let mut a: Z2_64N<80> = rng.sample(&base_dist);
        let mut b: Z2_64N<80> = Z2_64N {
            chunks: std::array::from_fn(|_| 0xffffffffffffffff),
        };
        let mut r = a.add(&b);
        let mut c = a.clone();
        c.add_assign(&b);
        b.add_assign(&a);
        let mut one: Z2_64N<80> = Z2_64N {
            chunks: std::array::from_fn(|_| 0),
        };
        one.chunks[0] = 1;
        r.add_assign(&one);
        a = c.add(&one);
        b.add_assign(&one);
        assert!(r == a);
        assert!(r == b);
    }
}

impl<const N: usize> ClosedSubDyn<()> for Z2_64N<N> {
    fn sub_d(&self, rhs: &Self, _ctx: &()) -> Self {
        let mut borrow = false;
        Self {
            chunks: std::array::from_fn(|n| {
                let r = self.chunks[n].borrowing_sub(rhs.chunks[n], borrow);
                borrow = r.1;
                r.0
            }),
        }
    }

    fn sub_assign_d(&mut self, rhs: &Self, _ctx: &()) -> () {
        let mut borrow = false;
        for n in 0..N {
            (self.chunks[n], borrow) = self.chunks[n].borrowing_sub(rhs.chunks[n], borrow);
        }
    }
}

#[test]
fn sub_test() {
    use rand::rngs::mock::StepRng;
    let mut rng = StepRng::new(0, 0x54825a7f54825a7f);
    let base_dist = StandardDyn::new(&());
    for _ in 0..100 {
        let a: Z2_64N<80> = rng.sample(&base_dist);
        let mut one: Z2_64N<80> = Z2_64N {
            chunks: std::array::from_fn(|_| 0),
        };
        one.chunks[0] = 1;
        let b = a.add(&one);
        let r = a.sub_d(&b, &());
        let z: Z2_64N<80> = Z2_64N {
            chunks: std::array::from_fn(|_| 0xffffffffffffffff),
        };
        assert!(r == z);
    }
}

impl<const N: usize> ZeroDyn<()> for Z2_64N<N> {
    fn zero_d(_ctx: &()) -> Self {
        Self {
            chunks: std::array::from_fn(|_| 0),
        }
    }
}

impl<const N: usize> ClosedMulDyn<()> for Z2_64N<N> {
    fn mul_d(&self, rhs: &Self, _ctx: &()) -> Self {
        // TODO: optimize (Karatsuba, etc.)
        let mut carry0: u64 = 0;
        let mut carry1: u64 = 0;
        Self {
            chunks: std::array::from_fn(|n| {
                let mut r: u64 = carry0;
                carry0 = carry1;
                carry1 = 0;
                for m in 0..=n {
                    let (rl, rh) = self.chunks[m].widening_mul(rhs.chunks[n - m]);
                    let mut c = false;
                    (r, c) = r.carrying_add(rl, c);
                    (carry0, c) = carry0.carrying_add(rh, c);
                    (carry1, _) = carry1.carrying_add(0, c);
                }
                r
            }),
        }
    }
}

#[test]
fn mul_test() {
    use rand::rngs::mock::StepRng;
    let mut rng = StepRng::new(0, 0x54825a7f54825a7f);
    let base_dist = StandardDyn::new(&());
    for _ in 0..100 {
        let a: Z2_64N<80> = rng.sample(&base_dist);
        let b: Z2_64N<80> = Z2_64N {
            chunks: std::array::from_fn(|_| 0xffffffffffffffff),
        };
        let r = a.mul_d(&b, &());
        let z = r.mul_d(&b, &());
        assert!(z == a);
    }
}

impl<const N: usize> OneDyn<()> for Z2_64N<N> {
    fn one_d(_ctx: &()) -> Self {
        Self {
            chunks: std::array::from_fn(|n| if n == 0 { 1 } else { 0 }),
        }
    }
}

impl<const N: usize> Distribution<Z2_64N<N>> for StandardDyn<'_, ()> {
    fn sample<R: ?Sized + Rng>(&self, rng: &mut R) -> Z2_64N<N> {
        Z2_64N {
            chunks: std::array::from_fn(|_| rng.sample(Standard)),
        }
    }
}
