use num_traits::One;
use num_traits::Zero;

/// Large signed integers.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct Large<const N: usize> {
    pub words: [u64; N],
}

impl<const N: usize> std::fmt::Debug for Large<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for i in (0..N).rev() {
            write!(f, "{:016x}", self.words[i])?;
        }
        Ok(())
    }
}

impl<const N: usize> rand::distributions::Distribution<Large<N>> for rand::distributions::Standard {
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Large<N> {
        let mut r = [0; N];
        for i in 0..N {
            r[i] = rng.next_u64();
        }
        Large { words: r }
    }
}

impl<const N: usize> num_traits::Zero for Large<N> {
    fn zero() -> Self {
        Self {
            words: [u64::zero(); N],
        }
    }

    fn is_zero(&self) -> bool {
        self.words.iter().all(|x| x.is_zero())
    }
}

impl<const N: usize> num_traits::FromPrimitive for Large<N> {
    fn from_i64(n: i64) -> Option<Self> {
        Some(n.into())
    }

    fn from_u64(n: u64) -> Option<Self> {
        Some(n.into())
    }
}

impl<const N: usize> std::ops::AddAssign<&Large<N>> for Large<N> {
    fn add_assign(&mut self, rhs: &Self) {
        let mut carry: u64 = 0;
        for i in 0..N {
            let tmp = self.words[i] as u128 + rhs.words[i] as u128 + carry as u128;
            carry = (tmp >> 64) as u64;
            self.words[i] = tmp as u64
        }
    }
}

impl<const N: usize> std::ops::AddAssign<Self> for Large<N> {
    fn add_assign(&mut self, rhs: Self) {
        *self += &rhs;
    }
}

impl<const N: usize> std::ops::Add<&Large<N>> for &Large<N> {
    type Output = Large<N>;

    fn add(self, rhs: &Large<N>) -> Self::Output {
        let mut r = self.clone();
        r += rhs;
        r
    }
}

impl<const N: usize> std::ops::Add<Self> for Large<N> {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl<const N: usize> num_traits::WrappingAdd for Large<N> {
    fn wrapping_add(&self, v: &Self) -> Self {
        self + v
    }
}

#[test]
fn add_test() {
    let a = Large::<3>::from(0xffffffffffffffff_u64);
    let result = a + a;
    assert_eq!(result.words[2], 0x0);
    assert_eq!(result.words[1], 0x1);
    assert_eq!(result.words[0], 0xfffffffffffffffe);
}

impl<const N: usize> std::ops::SubAssign<&Self> for Large<N> {
    fn sub_assign(&mut self, rhs: &Self) {
        let mut carry: u64 = 0;
        for i in 0..N {
            let tmp = (self.words[i] as u128)
                .wrapping_sub(rhs.words[i] as u128)
                .wrapping_add(carry as i64 as i128 as u128);
            carry = (tmp >> 64) as u64;
            self.words[i] = tmp as u64
        }
    }
}

impl<const N: usize> std::ops::SubAssign<Self> for Large<N> {
    fn sub_assign(&mut self, rhs: Self) {
        *self -= &rhs;
    }
}

impl<const N: usize> std::ops::Sub<&Large<N>> for &Large<N> {
    type Output = Large<N>;

    fn sub(self, rhs: &Large<N>) -> Self::Output {
        let mut r = self.clone();
        r -= rhs;
        r
    }
}

impl<const N: usize> std::ops::Sub<Self> for Large<N> {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<const N: usize> num_traits::WrappingSub for Large<N> {
    fn wrapping_sub(&self, v: &Self) -> Self {
        self - v
    }
}

#[test]
fn sub_test() {
    let a = Large::<3>::from(0x1_u64);
    let result = a - a - a;
    assert_eq!(result.words[2], 0xffffffffffffffff);
    assert_eq!(result.words[1], 0xffffffffffffffff);
    assert_eq!(result.words[0], 0xffffffffffffffff);
}

fn long_mul<const N: usize, const M: usize>(&lhs: &Large<N>, rhs: &Large<M>) -> Large<{ N + M }> {
    let mut r = Large::zero();
    for i in 0..N {
        let mut carry = 0;
        for j in 0..M {
            let tmp = r.words[i + j];
            (r.words[i + j], carry) = lhs.words[i].carrying_mul(rhs.words[j], carry);
            let mut carry2 = false;
            (r.words[i + j], carry2) = r.words[i + j].carrying_add(tmp, false);
            carry += if carry2 { 1 } else { 0 };
        }
        r.words[i + M] += carry;
    }
    r
}

impl<const N: usize, const M: usize> std::ops::Mul<&Large<M>> for &Large<N>
where
    [(); N + M]:,
{
    type Output = Large<{ N + M }>;

    fn mul(self, rhs: &Large<M>) -> Self::Output {
        if self.words[N - 1] & (1 << 63) != 0 {
            if rhs.words[M - 1] & (1 << 63) != 0 {
                long_mul(&(&Large::zero() - self), &(&Large::zero() - rhs))
            } else {
                &Large::zero() - &long_mul(&(&Large::zero() - self), rhs)
            }
        } else if rhs.words[M - 1] & (1 << 63) != 0 {
            &Large::zero() - &long_mul(self, &(&Large::zero() - rhs))
        } else {
            long_mul(self, rhs)
        }
    }
}

impl<const N: usize> Large<N> {
    pub fn umul<const M: usize>(&self, rhs: &Large<M>) -> Large<{ N + M }> {
        long_mul(self, rhs)
    }
}

impl<const N: usize, const M: usize> std::ops::Mul<Large<M>> for Large<N>
where
    [(); N + M]:,
{
    type Output = Large<{ N + M }>;

    fn mul(self, rhs: Large<M>) -> Self::Output {
        &self * &rhs
    }
}

use crate::WideningMul;
impl<const N: usize> WideningMul for Large<N>
where
    [(); { N + N }]:,
{
    fn wdmul(&self, other: &Self) -> (Self, Self) {
        let r: Large<{ N + N }> = self * other;
        let (low, high) = r.words.split_at(N);
        (
            Large {
                words: (*low).try_into().unwrap(),
            },
            Large {
                words: (*high).try_into().unwrap(),
            },
        )
    }
}

use crate::WrappingMul;
impl<const N: usize> WrappingMul for Large<N> {
    fn wpmul(&self, rhs: &Self) -> Self {
        let mut r = Self::zero();
        for i in 0..N {
            let mut carry = 0;
            for j in 0..(N - i) {
                let tmp = r.words[i + j];
                (r.words[i + j], carry) = self.words[i].carrying_mul(rhs.words[j], carry);
                let mut carry2 = false;
                (r.words[i + j], carry2) = r.words[i + j].carrying_add(tmp, false);
                carry += if carry2 { 1 } else { 0 };
            }
        }
        r
    }
}

#[test]
fn mul_test() {
    let a = Large::<1>::from(0x100000001_u64);
    let b = a * a;
    let c = b * b;
    let d = b * a;
    assert_eq!(c.words[3], 0x0);
    assert_eq!(c.words[2], 0x1);
    assert_eq!(c.words[1], 0x400000006);
    assert_eq!(c.words[0], 0x400000001);
    assert_eq!(d.words[2], 0x0);
    assert_eq!(d.words[1], 0x100000003);
    assert_eq!(d.words[0], 0x300000001);
}

#[test]
fn mul_test_signed() {
    let a = Large::zero() - Large::<1>::from(0x100000001_u64);
    let b = a * a;
    let c = b * b;
    let d = Large::zero() - b * a;
    assert_eq!(c.words[3], 0x0);
    assert_eq!(c.words[2], 0x1);
    assert_eq!(c.words[1], 0x400000006);
    assert_eq!(c.words[0], 0x400000001);
    assert_eq!(d.words[2], 0x0);
    assert_eq!(d.words[1], 0x100000003);
    assert_eq!(d.words[0], 0x300000001);
}

impl<const N: usize> Ord for Large<N> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        for i in (0..N).rev() {
            if self.words[i] != other.words[i] {
                return self.words[i].cmp(&other.words[i]);
            }
        }
        std::cmp::Ordering::Equal
    }
}

impl<const N: usize> PartialOrd for Large<N> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<const N: usize> From<u64> for Large<N> {
    fn from(value: u64) -> Self {
        let mut r = [0; N];
        r[0] = value;
        Self { words: r }
    }
}

impl<const N: usize> From<i64> for Large<N> {
    fn from(value: i64) -> Self {
        let mut r = [0xffffffffffffffff; N];
        r[0] = value as u64;
        Self { words: r }
    }
}

impl<const N: usize> Large<N> {
    pub fn expand<const M: usize>(&self) -> Large<{ N + M }>
    where
        [(); N + M]:,
    {
        let mut r = [0; N + M];
        for i in 0..N {
            r[i] = self.words[i];
        }
        Large { words: r }
    }

    pub fn extend<const M: usize>(&self) -> Large<{ N + M }>
    where
        [(); N + M]:,
    {
        let val = if self.words[N - 1] & (1 << 63) != 0 {
            0xffffffffffffffff
        } else {
            0
        };
        let mut r = [val; N + M];
        for i in 0..N {
            r[i] = self.words[i];
        }
        Large { words: r }
    }

    fn contract<const M: usize>(&self) -> Large<{ N - M }>
    where
        [(); N - M]:,
    {
        for i in N - M..N {
            debug_assert!(self.words[i] == 0);
        }
        Large {
            words: self.words[0..N - M].try_into().unwrap(),
        }
    }

    fn convert_identical<const M: usize>(&self) -> Large<M> {
        debug_assert!(N == M);
        Large {
            words: self.words[0..N].try_into().unwrap(),
        }
    }

    fn append_digit(&self, digit: u64) -> Large<{ N + 1 }>
    where
        [(); N + 1]:,
    {
        let mut r = [0; N + 1];
        r[0] = digit;
        for i in 0..N {
            r[i + 1] = self.words[i];
        }
        Large { words: r }
    }

    // perform a division where the quotient is a single word long
    fn div_step(a: &Large<{ N + 1 }>, b: &Self, leading_zeros: usize) -> (u64, Self)
    where
        [(); N + 1 - 1]:,
    {
        let dividend =
            ((a.words[N - leading_zeros] as u128) << 64) | (a.words[N - leading_zeros - 1] as u128);
        let divisor = b.words[N - leading_zeros - 1] as u128;
        let mut q = (dividend / divisor) as u64;
        if N == 1 {
            return (q, ((dividend % divisor) as u64).into());
        }
        let mut product = b.clone().umul(&Large::<1>::from(q));
        if *a < product {
            q = (dividend / (divisor + 1)) as u64;
            product = b.clone().umul(&Large::<1>::from(q));
        }
        debug_assert!(*a >= product);
        let mut diff = a.clone() - product;
        if diff >= b.expand::<1>() {
            let (q2, r) = Self::div_step(&diff, b, leading_zeros);
            q += q2;
            product = b.clone().umul(&Large::<1>::from(q));
            debug_assert!(*a >= product);
            diff = a.clone() - product;
            debug_assert!(diff < b.expand::<1>());
            return (q, r);
        }
        debug_assert!(diff < b.expand::<1>());
        let mut r = diff.contract::<1>().convert_identical::<N>();
        (q, r)
    }

    // perform an unsigned division
    fn div_long<const M: usize>(&self, other: &Large<M>) -> (Self, Large<M>)
    where
        [(); M + 1]:,
        [(); M + 1 - 1]:,
    {
        let mut leading_zeros = 0;
        for i in (0..M).rev() {
            if other.words[i] != 0 {
                break;
            }
            leading_zeros += 1;
        }
        let mut r: Large<M> = Large { words: [0; M] };
        let mut q_list: Vec<_> = (0..N).map(|_| 0).collect();
        for i in (0..N).rev() {
            let next_digit = self.words[i];
            let dividend = r.append_digit(next_digit);
            let mut q_digit = 0;
            (q_digit, r) = Large::div_step(&dividend, other, leading_zeros);
            q_list[i] = q_digit;
        }
        let q = Large {
            words: q_list.try_into().unwrap(),
        };
        (q, r)
    }
}

impl<const N: usize, const M: usize> std::ops::Div<&Large<M>> for &Large<N>
where
    [(); M + 1]:,
    [(); M + 1 - 1]:,
{
    type Output = Large<N>;

    fn div(self, rhs: &Large<M>) -> Self::Output {
        if self.words[N - 1] & (1 << 63) != 0 {
            let (q, r) = (&Large::zero() - &self).div_long(&rhs);
            &Large::zero() - &q
        } else {
            let (q, r) = self.div_long(&rhs);
            q
        }
    }
}

impl<const N: usize, const M: usize> std::ops::Div<Large<M>> for Large<N>
where
    [(); M + 1]:,
    [(); M + 1 - 1]:,
{
    type Output = Self;

    fn div(self, rhs: Large<M>) -> Self::Output {
        &self / &rhs
    }
}

#[test]
fn div_test() {
    let a = Large::<1>::from(0x100000001_u64);
    let b = a * a;
    let c = b * b + 3_u64.into();
    let d = c / b;
    let e = c % b;
    assert_eq!(d.words[3], 0x0);
    assert_eq!(d.words[2], 0x0);
    assert_eq!(d.words[1], 0x1);
    assert_eq!(d.words[0], 0x200000001);
    assert_eq!(e.words[0], 0x3);
}

#[test]
fn div_test_signed() {
    let a = Large::zero() - Large::<1>::from(0x100000001_u64);
    let b = a * a;
    let c = b * a + 3_u64.into();
    let d = c / b;
    let e = c % Large::<1>::from(0x100000001_u64);
    assert_eq!(d.words[2], 0xffffffffffffffff);
    assert_eq!(d.words[1], 0xffffffffffffffff);
    assert_eq!(d.words[0], a.words[0] + 1);
    assert_eq!(e.words[0], 0x3);
}

impl<const N: usize, const M: usize> std::ops::DivAssign<&Large<M>> for Large<N>
where
    [(); M + 1]:,
    [(); M + 1 - 1]:,
{
    fn div_assign(&mut self, rhs: &Large<M>) {
        *self = &*self / rhs;
    }
}

impl<const N: usize, const M: usize> std::ops::DivAssign<Large<M>> for Large<N>
where
    [(); M + 1]:,
    [(); M + 1 - 1]:,
{
    fn div_assign(&mut self, rhs: Large<M>) {
        *self /= &rhs;
    }
}

impl<const N: usize, const M: usize> std::ops::Rem<&Large<M>> for &Large<N>
where
    [(); M + 1]:,
    [(); M + 1 - 1]:,
{
    type Output = Large<M>;

    fn rem(self, rhs: &Large<M>) -> Self::Output {
        if self.words[N - 1] & (1 << 63) != 0 {
            let (q, r) = (&Large::zero() - &self).div_long(&rhs);
            /*&Large::zero()*/
            rhs - &r
        } else {
            let (q, r) = self.div_long(&rhs);
            r
        }
    }
}

impl<const N: usize, const M: usize> std::ops::Rem<Large<M>> for Large<N>
where
    [(); M + 1]:,
    [(); M + 1 - 1]:,
{
    type Output = Large<M>;

    fn rem(self, rhs: Large<M>) -> Self::Output {
        &self % &rhs
    }
}
