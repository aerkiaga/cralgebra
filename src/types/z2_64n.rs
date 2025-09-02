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
        /*let mut chunks = std::array::from_fn(|_| 0);
        let mut carry: u128 = 0;
        for n in 0..N {
            let mut r: u64 = 0;
            let mut c = false;
            for m in 0..n {
                let (rl, rh) = self.chunks[m].widening_mul(rhs.chunks[n - m]);
                (r, c) = r.carrying_add(rl, c);
                carry += rh as u128;
            }
            chunks[n] = r;
        }
        Self {
            chunks,
        }*/
        let mut carry: u128 = 0;
        Self {
            chunks: std::array::from_fn(|n| {
                let mut r: u64 = (carry & 0xffffffffffffffff) as u64;
                carry >>= 64;
                let mut c = false;
                for m in 0..n {
                    let (rl, rh) = self.chunks[m].widening_mul(rhs.chunks[n - m]);
                    (r, c) = r.carrying_add(rl, c);
                    carry += rh as u128;
                }
                r
            }),
        }
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
