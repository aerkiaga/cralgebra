use crate::*;
use std::mem::MaybeUninit;

/// Discrete Gaussian distribution.
///
/// ```rust
/// # #![feature(generic_const_exprs)]
/// # use crtypes_algebra::{Gaussian, Modular};
/// # use rand::distributions::Distribution;
/// let gauss = Gaussian::<10>::new(0.5);
/// let mut rng = rand::rngs::mock::StepRng::new(0x547273829375, 0x546372839465);
/// let s: Modular<10, u8> = gauss.sample(&mut rng);
/// assert_eq!(s.inner, 0);
/// ```
pub struct Gaussian<const N: u128>
where
    [(); N as usize]:,
{
    cdf_table: [f64; N as usize],
}

fn pdf(x: f64, std_dev: f64) -> f64 {
    f64::exp(-std::f64::consts::PI * x * x / std_dev / std_dev)
}

impl<const N: u128> Gaussian<N>
where
    [(); N as usize]:,
{
    pub fn new(std_dev: f64) -> Self {
        debug_assert!(N < usize::MAX as u128);
        let mut r = Self {
            cdf_table: [0.0; N as usize],
        };
        for i in 0..N as usize {
            let x = -(N as isize + 1) / 2 + 1 + i as isize;
            r.cdf_table[i] = pdf(x as f64, std_dev);
        }
        let total: f64 = r.cdf_table.iter().sum();
        let mut c = 0.0;
        for i in 0..N as usize {
            r.cdf_table[i] /= total;
            let old_c = c;
            c += r.cdf_table[i];
            r.cdf_table[i] = old_c;
        }
        r
    }
}

impl<const M: u128, T> rand::distributions::Distribution<Modular<M, T>> for Gaussian<M>
where
    modular::Modular<M, T>: From<u128>,
    [(); M as usize]:,
{
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Modular<M, T> {
        let v: f64 = rng.sample(rand::distributions::Standard);
        let mut low = 0;
        let mut high = M as usize - 1;
        while low < high {
            let mid = (low + high + 1) / 2;
            if self.cdf_table[mid] > v {
                high = mid - 1;
            } else {
                low = mid
            }
        }
        let i = low;
        let x = -(M as isize + 1) / 2 + 1 + i as isize;
        let ux = if x >= 0 { x as u128 } else { M - (-x) as u128 };
        Modular::from(ux)
    }
}

impl<const N: usize, const M: u128, T> rand::distributions::Distribution<PolyRing<N, Modular<M, T>>>
    for Gaussian<M>
where
    modular::Modular<M, T>: From<u128>,
    [(); M as usize]:,
{
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> PolyRing<N, Modular<M, T>> {
        let mut r: [Modular<M, T>; N] = unsafe { MaybeUninit::uninit().assume_init() };
        for i in 0..N {
            r[i] = self.sample(rng);
        }
        r.into()
    }
}
