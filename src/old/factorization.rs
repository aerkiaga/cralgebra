use crate::*;
use noether::*;
use num_traits::*;
use std::ops::*;

fn prime_factors_naive<T: Clone + Zero + ClosedAddAssign + One + ClosedMul + Euclid + PartialOrd>(
    mut n: T,
) -> Vec<T> {
    debug_assert!(!n.is_zero());
    debug_assert!(!n.is_one());
    let mut r = vec![];
    let mut x = T::one() + T::one();
    while x.clone() * x.clone() <= n {
        if n.clone().rem_euclid(x.clone()).is_zero() {
            r.push(x.clone());
            n = n.div_euclid(&x);
            while n.clone().rem_euclid(x.clone()).is_zero() {
                n = n.div_euclid(&x);
            }
        }
        x += T::one();
    }
    r
}

fn pollard_rho<T: Clone + Zero + ClosedAdd + ClosedSub + One + ClosedMul + Euclid + PartialOrd>(
    n: T,
) -> Option<T> {
    let mut x = T::one() + T::one();
    let mut y = T::one() + T::one();
    let mut d = T::one();
    let g = |z: T| (z.clone() * z + T::one()).rem_euclid(n.clone());
    while d.is_one() {
        x = g(x);
        y = g(g(y));
        let diff = if x > y {
            x.clone() - y.clone()
        } else {
            y.clone() - x.clone()
        };
        d = diff.gcd(n.clone());
    }
    if d == n {
        None
    } else {
        Some(d)
    }
}

fn sieve_erathosthenes(n: usize) -> Vec<usize> {
	let mut sieve = Vec::with_capacity(n + 1);
	sieve.fill(false);
    sieve[0] = true;
    sieve[1] = true;
    for i in 2..n.isqrt() + 1 {
        if !sieve[i] {
            for j in (i * i..n + 1).step_by(i) {
                sieve[j] = true
            }
        }
    }
    let mut r = vec![];
    for x in 2..n + 1 {
    	r.push(x);
    }
    r
}

/*fn find_base<T>(n: T) {
	usize max_base = 100;
	let primes = sieve_erathosthenes(max_base);
	for p in primes {
		
	}
}

fn prime_factors_quadratic_sieve<T>(n: T) {
	let base = quadratic_sieve_find_base(n);
}*/

pub trait Factorization:
    Clone + Zero + ClosedAddAssign + One + ClosedMul + Euclid + PartialOrd
{
    fn prime_factors(self) -> Vec<Self> {
        prime_factors_naive(self)
    }
}

impl Factorization for u8 {}
impl Factorization for u16 {}
impl Factorization for u32 {}
impl Factorization for u64 {}
impl Factorization for u128 {}
