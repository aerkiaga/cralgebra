use noether::*;
use num_traits::*;
use std::ops::*;

fn gcd_euclidean<T: Clone + Zero + Euclid + PartialOrd>(mut a: T, mut b: T) -> T {
    loop {
        if a < b {
            (a, b) = (b, a);
        }
        if b.is_zero() {
            return a;
        }
        a = a.rem_euclid(b.clone());
    }
}

pub trait Gcd: Clone + Zero + Euclid + PartialOrd {
    fn gcd(self, rhs: Self) -> Self {
        gcd_euclidean(self, rhs)
    }
}

impl<T: Clone + Zero + Euclid + PartialOrd> Gcd for T {}
