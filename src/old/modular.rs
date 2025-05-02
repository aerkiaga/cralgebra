use crate::*;
use noether::*;
use num_traits::*;
use std::mem::MaybeUninit;
use std::ops::*;

#[cfg(test)]
extern crate test;

/// Implements modular arithmetic over the integers.
///
/// Described by an ideal parameter `M`,
/// values wrap around so that this value is
/// equivalent to zero. The inner type `T`
/// must be able to represent all possible values.
///
/// Module change operations must be done manually,
/// so that the appropriate semantics are used.
/// This could involve converting to either a signed
/// or unsigned value, possibly taking a modulo
/// or quotient, then converting to the desired type.
///
/// Uses debug assertions to ensure that
/// the underlying type is large enough,
/// but will not check whether division
/// and multiplicative inverse are valid,
/// which is only the case **if `M` is prime**.
///
/// # Examples
/// ```rust
/// # use crtypes_algebra::Modular;
/// // Addition, subtraction and multiplication
/// let a: Modular<10, u8> = Modular::from(4 as u8);
/// let b: Modular<10, u8> = Modular::from(7 as u8);
/// assert_eq!((a + b).inner, 1);
/// assert_eq!((a * b).inner, 8);
/// assert_eq!((a - b).inner, 7);
/// // Division is only valid for prime modulo
/// let a: Modular<11, u8> = Modular::from(4 as u8);
/// let b: Modular<11, u8> = Modular::from(2 as u8);
/// assert_eq!((a / b).inner, 2);
/// ```
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(transparent)]
pub struct Modular<const M: u128, T: Sized> {
    /// The underlying raw integer.
    pub inner: T,
}

pub const fn expand_ratio(a: u128, b: u128) -> usize {
    let rounded_down = a.ilog(b);
    if a > b.pow(rounded_down) {
        rounded_down as usize + 1
    } else {
        rounded_down as usize
    }
}

impl<const M: u128, T: Into<u128>> Modular<M, T> {
    /// Expands a `Modular` into multiple digits
    /// with a smaller base.
    ///
    /// # Example
    /// ```rust
    /// # #![feature(generic_const_exprs)]
    /// # use crtypes_algebra::Modular;
    /// let a = Modular::<100, u8>::from(58 as u8);
    /// let [d1, d2] = a.expand_digits::<10, u8>();
    /// assert_eq!(d1.inner, 8);
    /// assert_eq!(d2.inner, 5);
    /// ```
    pub fn expand_digits<const M2: u128, T2>(self) -> [Modular<M2, T2>; expand_ratio(M, M2)]
    where
        Modular<M2, T2>: From<u128>,
    {
        debug_assert!(M2 <= M);
        let mut r: [Modular<M2, T2>; expand_ratio(M, M2)] =
            unsafe { MaybeUninit::uninit().assume_init() };
        let mut x: u128 = self.inner.into();
        for i in 0..expand_ratio(M, M2) {
            r[i] = (x % M2).into();
            x /= M2;
        }
        r
    }
}

impl<const M: u128, T: Clone> Modular<M, T> {
    //TODO: document
    pub fn contract_digits<const M2: u128, T2>(x: [Self; expand_ratio(M2, M)]) -> Modular<M2, T2>
    where
        Modular<M2, T2>: num_traits::Zero + From<u128>,
        T2: From<T> + MulAssign + AddAssign,
    {
        debug_assert!(M2 >= M);
        let mut r: Modular<M2, T2> = Modular::zero();
        for i in (0..expand_ratio(M2, M)).rev() {
            r.inner *= Modular::<M2, T2>::from(M).inner;
            r.inner += T2::from(x[i].inner.clone());
        }
        r
    }
}

impl<const M: u128, T: Into<u128>> Modular<M, T> {
    /// Compresses a `Modular` into a smaller modulus.
    ///
    /// # Example
    /// ```rust
    /// # use crtypes_algebra::Modular;
    /// let a: Modular<100, u8> = Modular::from(26 as u8);
    /// let b: Modular<100, u8> = Modular::from(72 as u8);
    /// assert_eq!(a.switch_mod::<10, u8>().inner, 3);
    /// assert_eq!(b.switch_mod::<10, u8>().inner, 7);
    /// ```
    pub fn switch_mod<const M2: u128, T2>(self) -> Modular<M2, T2>
    where
        Modular<M2, T2>: From<u128>,
    {
        debug_assert!(M2 <= M);
        Modular::from((self.inner.into() * M2 + M / 2) / M)
    }
}

//   ____                              _
//  / ___|___  _ ____   _____ _ __ ___(_) ___  _ __
// | |   / _ \| '_ \ \ / / _ \ '__/ __| |/ _ \| '_ \
// | |__| (_) | | | \ V /  __/ |  \__ \ | (_) | | | |
//  \____\___/|_| |_|\_/ \___|_|  |___/_|\___/|_| |_|
//

impl<const M: u128, T: FromPrimitive> FromPrimitive for Modular<M, T> {
    fn from_u64(n: u64) -> Option<Self> {
        if (n as u128) < M {
            T::from_u64(n).map(|x| Modular { inner: x })
        } else {
            None
        }
    }

    fn from_i64(n: i64) -> Option<Self> {
        let un = if n >= 0 { n as u128 } else { M - -n as u128 };
        if (un as u128) < M {
            T::from_u128(un).map(|x| Modular { inner: x })
        } else {
            None
        }
    }
}

impl<const M: u128, T: FromPrimitive> From<u8> for Modular<M, T> {
    fn from(value: u8) -> Self {
        Self::from_u8(value).unwrap()
    }
}

impl<const M: u128, T: FromPrimitive> From<i8> for Modular<M, T> {
    fn from(value: i8) -> Self {
        Self::from_i8(value).unwrap()
    }
}

impl<const M: u128, T: FromPrimitive> From<u16> for Modular<M, T> {
    fn from(value: u16) -> Self {
        Self::from_u16(value).unwrap()
    }
}

impl<const M: u128, T: FromPrimitive> From<i16> for Modular<M, T> {
    fn from(value: i16) -> Self {
        Self::from_i16(value).unwrap()
    }
}

impl<const M: u128, T: FromPrimitive> From<u32> for Modular<M, T> {
    fn from(value: u32) -> Self {
        Self::from_u32(value).unwrap()
    }
}

impl<const M: u128, T: FromPrimitive> From<i32> for Modular<M, T> {
    fn from(value: i32) -> Self {
        Self::from_i32(value).unwrap()
    }
}

impl<const M: u128, T: FromPrimitive> From<u64> for Modular<M, T> {
    fn from(value: u64) -> Self {
        Self::from_u64(value).unwrap()
    }
}

impl<const M: u128, T: FromPrimitive> From<i64> for Modular<M, T> {
    fn from(value: i64) -> Self {
        Self::from_i64(value).unwrap()
    }
}

impl<const M: u128, T: FromPrimitive> From<usize> for Modular<M, T> {
    fn from(value: usize) -> Self {
        Self::from_usize(value).unwrap()
    }
}

impl<const M: u128, T: FromPrimitive> From<isize> for Modular<M, T> {
    fn from(value: isize) -> Self {
        Self::from_isize(value).unwrap()
    }
}

impl<const M: u128> From<u128> for Modular<M, u128> {
    fn from(value: u128) -> Self {
        debug_assert!(value < M);
        Self { inner: value }
    }
}

impl<const M: u128> From<u128> for Modular<M, u8> {
    fn from(value: u128) -> Self {
        Self::from_u128(value).unwrap()
    }
}

impl<const M: u128> From<u128> for Modular<M, u16> {
    fn from(value: u128) -> Self {
        Self::from_u128(value).unwrap()
    }
}

impl<const M: u128> From<u128> for Modular<M, u32> {
    fn from(value: u128) -> Self {
        Self::from_u128(value).unwrap()
    }
}

impl<const M: u128> From<u128> for Modular<M, u64> {
    fn from(value: u128) -> Self {
        Self::from_u128(value).unwrap()
    }
}

//     _       _     _ _ _   _
//    / \   __| | __| (_) |_(_)_   _____
//   / _ \ / _` |/ _` | | __| \ \ / / _ \
//  / ___ \ (_| | (_| | | |_| |\ V /  __/
// /_/   \_\__,_|\__,_|_|\__|_| \_/ \___|
//

impl<const M: u128, T: Zero> Zero for Modular<M, T>
where
    Modular<M, T>: ClosedAdd,
{
    fn zero() -> Self {
        Self { inner: T::zero() }
    }

    fn is_zero(&self) -> bool {
        self.inner.is_zero()
    }
}

impl<const M: u128, T: Into<u128> + PartialOrd + Zero + WrappingAdd + WrappingSub + One> Add
    for Modular<M, T>
where
    Modular<{ M + 1 }, T>: From<u128>,
{
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let sum = self.inner.wrapping_add(&rhs.inner);
        let power_of_two = M - 1 == T::zero().wrapping_sub(&T::one()).into();
        let r = if power_of_two {
            sum
        } else {
            let wraparound = M.wrapping_add(M - 1) > T::zero().wrapping_sub(&T::one()).into();
            if wraparound && sum < rhs.inner
                || !wraparound && sum > Modular::<{ M + 1 }, T>::from(M).inner
            {
                sum - Modular::<{ M + 1 }, T>::from(M).inner
            } else {
                sum
            }
        };
        Self { inner: r }
    }
}

#[bench]
fn add_u64_bench(bencher: &mut test::Bencher) {
    let a = test::black_box(Modular::<91, u64>::from(45));
    let b = test::black_box(Modular::<91, u64>::from(49));
    let c = test::black_box(Modular::<91, u64>::from(3));
    bencher.iter(|| test::black_box(a + b));
    bencher.iter(|| test::black_box(a + c));
}

#[bench]
fn add_u128_bench(bencher: &mut test::Bencher) {
    let a = test::black_box(Modular::<91, u128>::from(45));
    let b = test::black_box(Modular::<91, u128>::from(49));
    let c = test::black_box(Modular::<91, u128>::from(3));
    bencher.iter(|| test::black_box(a + b));
    bencher.iter(|| test::black_box(a + c));
}

impl<const M: u128, T: ~const AddCost<T>> const AddCost<Self> for Modular<M, T>
where
    Self: ClosedAdd,
{
    fn add_cost() -> f64 {
        T::add_cost() + 1.0
    }
}

impl<const M: u128, T: Copy> AddAssign<Self> for Modular<M, T>
where
    Modular<M, T>: Add<Output = Modular<M, T>>,
{
    fn add_assign(&mut self, rhs: Self) {
        self.inner = (*self + rhs).inner;
    }
}

impl<const M: u128, T: Into<u128> + PartialOrd + Zero + WrappingAdd + WrappingSub + One> Sub
    for Modular<M, T>
where
    Modular<{ M + 1 }, T>: From<u128>,
{
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let diff = self.inner.wrapping_sub(&rhs.inner);
        let power_of_two = M - 1 == T::zero().wrapping_sub(&T::one()).into();
        let r = if power_of_two {
            diff
        } else {
            if self.inner < diff {
                diff.wrapping_add(&Modular::<{ M + 1 }, T>::from(M).inner)
            } else {
                diff
            }
        };
        Self { inner: r }
    }
}

impl<const M: u128, T: Copy> SubAssign<Self> for Modular<M, T>
where
    Modular<M, T>: Sub<Output = Modular<M, T>>,
{
    fn sub_assign(&mut self, rhs: Self) {
        self.inner = (*self - rhs).inner;
    }
}

impl<const M: u128, T: num_traits::Zero> Neg for Modular<M, T>
where
    Self: Sub<Output = Self>,
{
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self { inner: T::zero() } - self
    }
}

impl<const M: u128, T: num_traits::Zero> std::iter::Sum for Modular<M, T>
where
    Modular<M, T>: From<T> + AddAssign,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        let mut r = T::zero().into();
        for x in iter {
            r += x;
        }
        r
    }
}

impl<const M: u128, T> AssociativeAddition for Modular<M, T> {}

impl<const M: u128, T> CommutativeAddition for Modular<M, T> {}

//  __  __       _ _   _       _ _           _   _
// |  \/  |_   _| | |_(_)_ __ | (_) ___ __ _| |_(_)_   _____
// | |\/| | | | | | __| | '_ \| | |/ __/ _` | __| \ \ / / _ \
// | |  | | |_| | | |_| | |_) | | | (_| (_| | |_| |\ V /  __/
// |_|  |_|\__,_|_|\__|_| .__/|_|_|\___\__,_|\__|_| \_/ \___|
//

impl<const M: u128, T: One> One for Modular<M, T>
where
    Self: Mul<Output = Self>,
{
    fn one() -> Self {
        debug_assert!(M > 1);
        Self { inner: T::one() }
    }
}

impl<const M: u128> Mul for Modular<M, u8> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        debug_assert!(M <= (u8::MAX as u128) + 1);
        if M <= 0x10 {
            Self {
                inner: (self.inner * rhs.inner) % M as u8,
            }
        } else {
            Self {
                inner: ((self.inner as u16 * rhs.inner as u16) % M as u16) as u8,
            }
        }
    }
}

impl<const M: u128> Mul for Modular<M, u16> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        debug_assert!(M <= (u16::MAX as u128) + 1);
        if M <= 0x100 {
            Self {
                inner: (self.inner * rhs.inner) % M as u16,
            }
        } else {
            Self {
                inner: ((self.inner as u32 * rhs.inner as u32) % M as u32) as u16,
            }
        }
    }
}

impl<const M: u128> Mul for Modular<M, u32> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        debug_assert!(M <= (u32::MAX as u128) + 1);
        if M <= 0x10000 {
            Self {
                inner: (self.inner * rhs.inner) % M as u32,
            }
        } else {
            Self {
                inner: ((self.inner as u64 * rhs.inner as u64) % M as u64) as u32,
            }
        }
    }
}

impl<const M: u128> Mul for Modular<M, u64> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        debug_assert!(M <= (u64::MAX as u128) + 1);
        if M <= 0x100000000 {
            Self {
                inner: (self.inner * rhs.inner) % M as u64,
            }
        } else {
            Self {
                inner: ((self.inner as u128 * rhs.inner as u128) % M) as u64,
            }
        }
    }
}

impl<const M: u128> Mul for Modular<M, u128>
where
    Modular<M, u128>: ClosedAdd,
{
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        if M <= 0x10000000000000000 {
            Self {
                inner: (self.inner * rhs.inner) % M,
            }
        } else {
            let (low, high) = self.inner.widening_mul(rhs.inner);
            let coeff = Self::from(u128::MAX % M) + Self::one();
            if high.is_zero() {
                Self::from(low % M)
            } else {
                let prod = Self::from(high) * coeff;
                Self::from(low % M) + prod
            }
        }
    }
}

#[bench]
fn mul_u64_bench(bencher: &mut test::Bencher) {
    let a = test::black_box(Modular::<91, u64>::from(45));
    let b = test::black_box(Modular::<91, u64>::from(49));
    bencher.iter(|| test::black_box(a * b));
}

#[bench]
fn mul_u64_bench2(bencher: &mut test::Bencher) {
    let a = test::black_box(Modular::<{ 1 << 40 }, u64>::from(45));
    let b = test::black_box(Modular::<{ 1 << 40 }, u64>::from(49));
    bencher.iter(|| test::black_box(a * b));
}

#[bench]
fn mul_u128_bench(bencher: &mut test::Bencher) {
    let a = test::black_box(Modular::<91, u128>::from(45));
    let b = test::black_box(Modular::<91, u128>::from(49));
    bencher.iter(|| test::black_box(a * b));
}

#[bench]
fn mul_u128_bench2(bencher: &mut test::Bencher) {
    let a = test::black_box(Modular::<{ 1 << 80 }, u128>::from(45));
    let b = test::black_box(Modular::<{ 1 << 80 }, u128>::from(49));
    bencher.iter(|| test::black_box(a * b));
}

impl<const M: u128, T: ~const MulCost<T> + ~const DivCost<T>> const MulCost<Self> for Modular<M, T>
where
    Self: ClosedMul,
{
    fn mul_cost() -> f64 {
        T::mul_cost() + T::div_cost()
    }
}

impl<const M: u128, T> MulAssign<Self> for Modular<M, T>
where
    Modular<M, T>: Clone + ClosedMul,
{
    fn mul_assign(&mut self, rhs: Self) {
        self.inner = (self.clone() * rhs).inner;
    }
}

impl<const M: u128, T> Pow<u128> for Modular<M, T>
where
    Modular<M, T>: Clone + ClosedMul + One,
{
    type Output = Self;

    fn pow(mut self, mut exp: u128) -> Self {
        let mut r = Self::one();
        while exp > 0 {
            if exp & 1 != 0 {
                r *= self.clone();
            }
            self *= self.clone();
            exp >>= 1;
        }
        r
    }
}

#[test]
fn pow_test() {
    let a: Modular<10, u8> = Modular::from(2 as u8);
    assert_eq!(a.pow(0).inner, 1);
    assert_eq!(a.pow(1).inner, 2);
    assert_eq!(a.pow(2).inner, 4);
    assert_eq!(a.pow(3).inner, 8);
    assert_eq!(a.pow(4).inner, 6);
    assert_eq!(a.pow(10).inner, 4);
    assert_eq!(a.pow(1000000000000000000).inner, 6);
}

impl<const M: u128, T> Inv for Modular<M, T>
where
    Modular<M, T>: Clone + ClosedMul + One,
{
    type Output = Self;

    fn inv(self) -> Self {
        self.pow(M - 2)
    }
}

#[test]
fn inv_test() {
    // 11 is prime
    let a: Modular<11, u8> = Modular::from(2 as u8);
    assert_eq!((a.inv() * a).inner, 1);
}

impl<const M: u128, T> Div for Modular<M, T>
where
    Self: Clone + ClosedMul + One,
{
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.inv()
    }
}

impl<const M: u128, T: Copy> DivAssign<Self> for Modular<M, T>
where
    Modular<M, T>: Div<Output = Modular<M, T>>,
{
    fn div_assign(&mut self, rhs: Self) {
        self.inner = (*self / rhs).inner;
    }
}

impl<const M: u128, T> Rem for Modular<M, T>
where
    Modular<M, T>: Zero,
{
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        Self::zero()
    }
}

impl<const M: u128, T> AssociativeMultiplication for Modular<M, T> {}

impl<const M: u128, T> CommutativeMultiplication for Modular<M, T> {}

impl<const M: u128, T> Distributive for Modular<M, T> {}

impl<const M: u128, T> Euclid for Modular<M, T>
where
    Modular<M, T>: Clone + ClosedDiv + ClosedRem,
{
    fn div_euclid(&self, v: &Self) -> Self {
        (*self).clone() / (*v).clone()
    }

    fn rem_euclid(&self, v: &Self) -> Self {
        (*self).clone() % (*v).clone()
    }
}

impl<const M: u128, T> Modular<M, T>
where
    Self: Field,
{
    pub fn primitive_root() -> Self {
        let prime_factors = (M - 1).prime_factors();
        let mut x = Self::one() + Self::one();
        loop {
            let mut found = true;
            for divisor in &prime_factors {
                if x.clone().pow(*divisor).is_one() {
                    found = false;
                    break;
                }
            }
            if found {
                return x;
            }
        }
        panic!("Field has no primitive roots");
    }
}

impl<const M: u128, T> RootsOfUnity for Modular<M, T>
where
    Self: Field,
{
    fn root_of_unity(n: u128) -> Self {
        let (q, r) = (M - 1).div_rem_euclid(&n);
        debug_assert!(
            r.is_zero(),
            "n-th root of unity is only defined if n divides M - 1"
        );
        let g = Self::primitive_root();
        g.pow(q)
    }
}

//  __  __ _              _ _
// |  \/  (_)___  ___ ___| | | __ _ _ __   ___  ___  _   _ ___
// | |\/| | / __|/ __/ _ \ | |/ _` | '_ \ / _ \/ _ \| | | / __|
// | |  | | \__ \ (_|  __/ | | (_| | | | |  __/ (_) | |_| \__ \
// |_|  |_|_|___/\___\___|_|_|\__,_|_| |_|\___|\___/ \__,_|___/
//

impl<const M: u128> rand::distributions::Distribution<Modular<M, u8>>
    for rand::distributions::Standard
{
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Modular<M, u8> {
        debug_assert!(M <= (u8::MAX as u128) + 1);
        if M <= (u8::MAX as u128) {
            Modular {
                inner: rng.gen_range(0..M as u8),
            }
        } else {
            Modular { inner: rng.gen() }
        }
    }
}

impl<const M: u128> rand::distributions::Distribution<Modular<M, u16>>
    for rand::distributions::Standard
{
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Modular<M, u16> {
        debug_assert!(M <= (u16::MAX as u128) + 1);
        if M <= (u16::MAX as u128) {
            Modular {
                inner: rng.gen_range(0..M as u16),
            }
        } else {
            Modular { inner: rng.gen() }
        }
    }
}

impl<const M: u128> rand::distributions::Distribution<Modular<M, u32>>
    for rand::distributions::Standard
{
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Modular<M, u32> {
        debug_assert!(M <= (u32::MAX as u128) + 1);
        if M <= (u32::MAX as u128) {
            Modular {
                inner: rng.gen_range(0..M as u32),
            }
        } else {
            Modular { inner: rng.gen() }
        }
    }
}

impl<const M: u128> rand::distributions::Distribution<Modular<M, u64>>
    for rand::distributions::Standard
{
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Modular<M, u64> {
        debug_assert!(M <= (u64::MAX as u128) + 1);
        if M <= (u64::MAX as u128) {
            Modular {
                inner: rng.gen_range(0..M as u64),
            }
        } else {
            Modular { inner: rng.gen() }
        }
    }
}

impl<const M: u128> rand::distributions::Distribution<Modular<M, u128>>
    for rand::distributions::Standard
{
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Modular<M, u128> {
        Modular {
            inner: rng.gen_range(0..M),
        }
    }
}
