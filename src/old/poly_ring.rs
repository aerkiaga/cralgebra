use crate::*;
use bit_reverse::ParallelReverse;
use noether::*;
use num_traits::*;
use std::mem::MaybeUninit;
use std::ops::*;
use std::sync::LazyLock;

#[cfg(test)]
extern crate test;

/// Implements arithmetic over `T`\[_x_\]/(_x_^`N` + 1).
///
/// That is, a `PolyRing` represents a
/// polynomial of degree `N` - 1, with
/// coefficients of type `T`, operations
/// on which "wrap around" so that 1 * _x_^`N` + 1
/// is equivalent to 0 (here 1 and 0
/// represent the multiplicative and additive
/// identity elements of `T`: `T::one()`
/// and `T::zero()`).
///
/// Notes regarding `N`:
/// - Division is only defined for `N` of either 1 or 2.
/// - The polynomial is cyclotomic if `N` is a power of 2.
#[derive(Clone)]
pub struct PolyRing<const N: usize, T> {
    /// The underlying coefficients, from constant to x^(`N` - 1).
    pub coefficients: [T; N],
}

impl<const N: usize, T: Clone + Zero + AddAssign + SubAssign + ClosedMul> PolyRing<N, T> {
    /// Multiply two `PolyRing` using the naïve algorithm.
    ///
    /// Running time is _O_(`N`^2).
    ///
    /// # Example
    /// ```rust
    /// # use crtypes_algebra::PolyRing;
    /// let a: PolyRing<2, u8> = [2, 3].into();
    /// let b: PolyRing<2, u8> = [4, 2].into();
    /// assert_eq!(a.mul_naive(b).coefficients, [2, 16]);
    /// ```
    pub fn mul_naive(self, rhs: Self) -> Self {
        let mut r = PolyRing {
            coefficients: std::array::from_fn(|_| T::zero()),
        };
        for i in 0..N {
            for j in 0..i + 1 {
                r.coefficients[i] += self.coefficients[j].clone() * rhs.coefficients[i - j].clone();
            }
        }
        for i in 0..N {
            for j in i + 1..N {
                r.coefficients[i] -= self.coefficients[j].clone() * rhs.coefficients[N - j].clone();
            }
        }
        r
    }
}

#[test]
fn mul_naive_test() {
    let a = PolyRing::<2, i8> {
        coefficients: [1, 1],
    };
    let b = PolyRing::<2, i8> {
        coefficients: [1, 2],
    };
    let c = a.mul_naive(b);
    assert_eq!(c.coefficients, [-1, 3]);
}

#[bench]
fn mul_naive_10_bench(bencher: &mut test::Bencher) {
    let a = test::black_box(PolyRing::<10, u64>::zero());
    let b = test::black_box(PolyRing::<10, u64>::zero());
    bencher.iter(|| test::black_box(a.clone().mul_naive(b.clone())));
}

#[bench]
fn mul_naive_100_bench(bencher: &mut test::Bencher) {
    let a = test::black_box(PolyRing::<100, u64>::zero());
    let b = test::black_box(PolyRing::<100, u64>::zero());
    bencher.iter(|| test::black_box(a.clone().mul_naive(b.clone())));
}

const fn mul_naive_cost<
    const N: usize,
    T: Clone + Zero + AddAssign + SubAssign + ClosedMul + ~const AddCost + ~const MulCost,
>() -> f64 {
    (T::add_cost() + T::mul_cost()) * (N as f64) * (N as f64)
}

impl<const N: usize, T: From<u128> + Field + RootsOfUnity> PolyRing<N, T> {
    const ROOTS: LazyLock<[T; N]> = LazyLock::new(|| {
        debug_assert!(N.is_power_of_two(), "NTT only supported for power of two N");
        let logN = N.ilog2();
        let root = T::root_of_unity(2 * N as u128);
        let mut cur = root.clone();
        let mut r = std::array::from_fn(|_| T::zero());
        for i in 0..N {
            let index = (i << (usize::BITS - logN)).swap_bits();
            r[index] = cur.clone();
            cur *= root.clone();
        }
        r
    });

    pub fn ntt(mut self) -> Self {
        let roots = Self::ROOTS.clone();
        let mut t = N;
        let mut m = 1;
        while m < N {
            t /= 2;
            for i in 0..m {
                let j1 = 2 * i * t;
                let j2 = j1 + t - 1;
                let s = &roots[m + i];
                for j in j1..=j2 {
                    let u = self.coefficients[j].clone();
                    let v = self.coefficients[j + t].clone() * s.clone();
                    self.coefficients[j] = u.clone() + v.clone();
                    self.coefficients[j + t] = u - v;
                }
            }
            m *= 2;
        }
        self
    }

    const IROOTS: LazyLock<[T; N]> = LazyLock::new(|| {
        debug_assert!(N.is_power_of_two(), "NTT only supported for power of two N");
        let logN = N.ilog2();
        let root = T::root_of_unity(2 * N as u128).inv();
        let mut cur = root.clone();
        let mut r = std::array::from_fn(|_| T::zero());
        for i in 0..N {
            let index = (i << (usize::BITS - logN)).swap_bits();
            r[index] = cur.clone();
            cur *= root.clone();
        }
        r
    });

    pub fn intt(mut self) -> Self {
        let iroots = Self::IROOTS.clone();
        let mut t = 1;
        let mut m = N;
        while m > 1 {
            let mut j1 = 0;
            let h = m / 2;
            for i in 0..h {
                let j2 = j1 + t - 1;
                let s = &iroots[h + i];
                for j in j1..=j2 {
                    let u = self.coefficients[j].clone();
                    let v = self.coefficients[j + t].clone();
                    self.coefficients[j] = u.clone() + v.clone();
                    self.coefficients[j + t] = (u - v) * s.clone();
                }
                j1 += 2 * t;
            }
            t *= 2;
            m /= 2;
        }
        let inv = T::one() / T::from(N as u128);
        for j in 0..N {
            self.coefficients[j] *= inv.clone();
        }
        self
    }

    // TODO: add documentation, including citation
    fn mul_ntt(self, rhs: Self) -> Self {
        let a_ntt = self.ntt();
        let b_ntt = rhs.ntt();
        let c_ntt =
            Self::from_fn(|i| a_ntt.coefficients[i].clone() * b_ntt.coefficients[i].clone());
        let c = c_ntt.intt();
        //Self::from_fn(|i| c.coefficients[i].clone() * iroots_reg[i].clone())
        c
    }
}

#[test]
fn mul_ntt_test() {
    let a = PolyRing::<2, Modular<5, u8>> {
        coefficients: [1.into(), 1.into()],
    };
    let b = PolyRing::<2, Modular<5, u8>> {
        coefficients: [1.into(), 2.into()],
    };
    let c = a.mul_ntt(b);
    assert_eq!(c.coefficients, [(-1).into(), 3.into()]);
}

#[bench]
fn ntt_16_bench(bencher: &mut test::Bencher) {
    let a = test::black_box(PolyRing::<16, Modular<97, u64>>::one());
    bencher.iter(|| test::black_box(a.clone().ntt()));
}

#[bench]
fn ntt_128_bench(bencher: &mut test::Bencher) {
    let a = test::black_box(PolyRing::<128, Modular<257, u64>>::one());
    bencher.iter(|| test::black_box(a.clone().ntt()));
}

#[bench]
fn ntt_8192_bench(bencher: &mut test::Bencher) {
    let a = test::black_box(PolyRing::<8192, Modular<65537, u64>>::one());
    bencher.iter(|| test::black_box(a.clone().ntt()));
}

const fn ntt_cost<
    const N: usize,
    T: From<u128> + Field + RootsOfUnity + ~const AddCost + ~const MulCost,
>() -> f64 {
    (u64::add_cost() * 2.0 + T::add_cost() * 2.0 + T::mul_cost() * 2.0 + 1.0)
        * N.ilog2() as f64
        * N as f64
}

const fn intt_cost<
    const N: usize,
    T: From<u128> + Field + RootsOfUnity + ~const AddCost + ~const MulCost,
>() -> f64 {
    ntt_cost::<N, T>() + N as f64 * T::mul_cost()
}

const fn mul_ntt_cost<
    const N: usize,
    T: From<u128> + Field + RootsOfUnity + ~const AddCost + ~const MulCost,
>() -> f64 {
    ntt_cost::<N, T>() + N as f64 * T::mul_cost() + intt_cost::<N, T>()
}

impl<const N: usize, T: Clone + std::ops::Neg<Output = T>> PolyRing<N, T> {
    /// Computes the result of applying the Frobenius endomorphism.
    ///
    /// This maps every _x_ to _x_^`l`.
    ///
    /// **Note: undefined behavior will result if `l` and `N` are not coprime.**
    /// The implementation does not currently check this.
    pub fn frobenius(&self, l: usize) -> Self
    where
        [(); { 2 * N as u128 } as usize]:,
    {
        debug_assert!(N <= usize::MAX / 2);
        debug_assert!(N <= u64::MAX as usize / 2);
        let mut r: [T; N] = unsafe { MaybeUninit::uninit().assume_init() };
        for i in 0..N {
            let mut x = Modular::<{ 2 * N as u128 }, u64>::from(i as u64);
            x = x.pow(l as u128);
            let is_negative = x.inner >= N as u64;
            let index = (x.inner % N as u64) as usize;
            r[index] = if is_negative {
                -self[i].clone()
            } else {
                self[i].clone()
            };
        }
        r.into()
    }
}

impl<const N: usize, T> From<[T; N]> for PolyRing<N, T> {
    fn from(value: [T; N]) -> Self {
        PolyRing {
            coefficients: value,
        }
    }
}

impl<const N: usize, T> PolyRing<N, T> {
    /// Initialize elements from a closure.
    pub fn from_fn<F: Fn(usize) -> T>(f: F) -> Self {
        PolyRing {
            coefficients: std::array::from_fn(f),
        }
    }
}

impl<const N: usize, T: Clone> PolyRing<N, T> {
    /// Map each element using `.into()`.
    pub fn map_into<U: From<T>>(self: PolyRing<N, T>) -> PolyRing<N, U> {
        let mut r: [U; N] = unsafe { MaybeUninit::uninit().assume_init() };
        for i in 0..N {
            r[i] = self.coefficients[i].clone().into();
        }
        PolyRing { coefficients: r }
    }
}

impl<const N: usize, T: Clone> PolyRing<N, T> {
    pub fn map<U, F: Fn(T) -> U>(self, f: F) -> PolyRing<N, U> {
        PolyRing {
            coefficients: std::array::from_fn(|i| f(self.coefficients[i].clone())),
        }
    }
}

impl<const N: usize, T: num_traits::Zero> num_traits::Zero for PolyRing<N, T>
where
    Self: std::ops::Add<Output = Self>,
{
    fn zero() -> Self {
        Self {
            coefficients: std::array::from_fn(|_| T::zero()),
        }
    }

    fn is_zero(&self) -> bool {
        self.coefficients.iter().all(|x| x.is_zero())
    }
}

impl<const N: usize, T> std::iter::Sum for PolyRing<N, T>
where
    PolyRing<N, T>: std::ops::Add<Output = PolyRing<N, T>> + num_traits::Zero,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        iter.reduce(|acc, e| acc + e).unwrap_or(Self::zero())
    }
}

impl<const N: usize, T: num_traits::One + num_traits::Zero> num_traits::One for PolyRing<N, T>
where
    Self: std::ops::Mul<Output = Self>,
{
    fn one() -> Self {
        Self {
            coefficients: std::array::from_fn(|i| if i == 0 { T::one() } else { T::zero() }),
        }
    }
}

impl<const N: usize, T: Clone + std::ops::MulAssign<T>> std::ops::Mul<T> for PolyRing<N, T> {
    type Output = Self;

    fn mul(mut self, rhs: T) -> Self::Output {
        for coeff in &mut self.coefficients {
            *coeff *= rhs.clone();
        }
        self
    }
}

/*impl<
        const N: usize,
        T: Clone
            + num_traits::Zero
            + num_traits::One
            + std::ops::AddAssign
            + std::ops::SubAssign
            + std::ops::Mul<Output = T>,
    > std::ops::Mul<PolyRing<N, T>> for PolyRing<N, T>
{
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        self.mul_naive(rhs)
    }
}*/

impl<const N: usize, T: From<u128> + Field + RootsOfUnity> std::ops::Mul<PolyRing<N, T>>
    for PolyRing<N, T>
{
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        self.mul_ntt(rhs)
    }
}

impl<const N: usize, T: std::ops::AddAssign> std::ops::Add for PolyRing<N, T> {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        for (i, coeff) in rhs.coefficients.into_iter().enumerate() {
            self.coefficients[i] += coeff;
        }
        self
    }
}

impl<const N: usize, T: std::ops::SubAssign> std::ops::Sub for PolyRing<N, T> {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        for (i, coeff) in rhs.coefficients.into_iter().enumerate() {
            self.coefficients[i] -= coeff;
        }
        self
    }
}

impl<const N: usize, T: std::ops::AddAssign> std::ops::AddAssign for PolyRing<N, T> {
    fn add_assign(&mut self, rhs: Self) {
        for (i, coeff) in rhs.coefficients.into_iter().enumerate() {
            self.coefficients[i] += coeff;
        }
    }
}

impl<const N: usize, T: Clone + std::ops::Neg<Output = T>> std::ops::Neg for PolyRing<N, T> {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        for i in 0..N {
            self.coefficients[i] = -self.coefficients[i].clone();
        }
        self
    }
}

impl<const N: usize, T: From<u128> + Field + RootsOfUnity> Inv for PolyRing<N, T> {
    type Output = Self;

    fn inv(self) -> Self::Output {
        self.ntt().map(|x| x.inv()).intt()
    }
}

impl<const N: usize, T> std::ops::Index<usize> for PolyRing<N, T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        &self.coefficients[index]
    }
}

impl<const N: usize, T> rand::distributions::Distribution<PolyRing<N, T>>
    for rand::distributions::Standard
where
    rand::distributions::Standard: rand::distributions::Distribution<T>,
{
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> PolyRing<N, T> {
        let mut r: [MaybeUninit<T>; N] = unsafe { MaybeUninit::uninit().assume_init() };
        for i in 0..N {
            r[i] = MaybeUninit::new(rng.sample(rand::distributions::Standard));
        }
        PolyRing {
            coefficients: unsafe { r.map(|x| x.assume_init()) },
        }
    }
}
