use crate::{WideningMul, WrappingMul};

/// Modular arithmetic in Montgomery form,
/// with manual modulo handling.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Montgomery<T> {
    inner: T,
}

/// Modulo context for Montgomery arithmetic.
#[derive(Clone, Copy)]
pub struct MontgomeryModulo<T> {
    // modulo
    m: T,
    // size in bits
    s: usize,
    // 2^2s, modulo m
    r2: Montgomery<T>,
    // inverse of m, modulo 2^s
    m_inv: T,
}

impl<
        T: Clone
            + num_traits::Zero
            + num_traits::FromPrimitive
            + num_traits::WrappingAdd
            + num_traits::WrappingSub
            + std::ops::Rem<T, Output = T>
            + std::cmp::Ord
            + WideningMul
            + WrappingMul,
    > MontgomeryModulo<T>
{
    fn inv_s(x: &T, mut s: usize) -> T {
        debug_assert!(s != 0);
        let lead = s.leading_zeros() + 1;
        let mut r = T::from_u64(1).unwrap();
        let two = T::from_u64(2).unwrap();
        for i in (lead..usize::BITS) {
            let bit = s & (1 << (usize::BITS - i - 1));
            r = r.wpmul(&two.wrapping_sub(&x.wpmul(&r)));
            if bit != 0 {
                r = r.wpmul(&r.wpmul(&x));
            }
        }
        r
    }

    fn montgomery_reduce_s(low: &T, high: &T, m: &T, s: usize, m_inv: &T) -> T {
        let q = low.wpmul(m_inv);
        let (_, w) = q.wdmul(m);
        let r = if high >= &w {
            high.wrapping_sub(&w)
        } else {
            high.wrapping_add(m).wrapping_sub(&w)
        };
        r
    }

    fn mul_montgomery_s(a: &T, b: &T, m: &T, s: usize, m_inv: &T) -> T {
        let (t_low, t_high) = a.wdmul(b);
        let r = Self::montgomery_reduce_s(&t_low, &t_high, m, s, m_inv);
        r
    }

    fn r2_s(x: &T, s: usize, m_inv: &T) -> T {
        debug_assert!(s != 0);
        let lead = s.leading_zeros() + 1;
        let mut r = T::zero().wrapping_sub(x) % x.clone();
        let two = T::from_u64(2).unwrap();
        r = r.wpmul(&two);
        if &r >= x {
            r = r.wrapping_sub(x);
        }
        for i in (lead..usize::BITS) {
            let bit = s & (1 << (usize::BITS - i - 1));
            r = Self::mul_montgomery_s(&r, &r, x, s, m_inv);
            if bit != 0 {
                r = r.wpmul(&two);
                if &r >= x {
                    r = r.wrapping_sub(x);
                }
            }
        }
        r
    }

    /// Creates a context for modulo `m`,
    /// where `T` is assumed to represent
    /// an `s`-bit number.
    pub fn new(m: T, s: usize) -> Self {
        let m_inv = Self::inv_s(&m, s);
        let inner = Self::r2_s(&m, s, &m_inv);
        Self {
            m: m,
            s: s,
            r2: Montgomery { inner: inner },
            m_inv: m_inv,
        }
    }

    /// Multiplies `a` by `b` modulo `m`.
    ///
    /// # Example
    /// ```rust
    /// # use crtypes_algebra::*;
    /// let modulo = 53_u32;
    /// let mg = MontgomeryModulo::new(modulo, u32::BITS as usize);
    /// let a = 45_u32;
    /// let a_mg = mg.encode(a);
    /// let b = 11_u32;
    /// let b_mg = mg.encode(b);
    /// let p_mg = mg.mul(&a_mg, &b_mg);
    /// let p = mg.decode(&p_mg);
    /// assert_eq!(p, (a * b) % modulo);
    /// ```
    pub fn mul(&self, a: &Montgomery<T>, b: &Montgomery<T>) -> Montgomery<T> {
        Montgomery {
            inner: Self::mul_montgomery_s(&a.inner, &b.inner, &self.m, self.s, &self.m_inv),
        }
    }

    /// Converts `x` to Montgomery form.
    ///
    /// # Example
    /// ```rust
    /// # use crtypes_algebra::*;
    /// let mg = MontgomeryModulo::new(53_u32, u32::BITS as usize);
    /// let x = 45_u32;
    /// let x_mg = mg.encode(x);
    /// assert_eq!(mg.decode(&x_mg), x);
    /// ```
    pub fn encode(&self, x: T) -> Montgomery<T> {
        self.mul(&Montgomery { inner: x }, &self.r2)
    }

    /// Converts `x` back from Montgomery form.
    pub fn decode(&self, x: &Montgomery<T>) -> T {
        Self::montgomery_reduce_s(&x.inner, &T::zero(), &self.m, self.s, &self.m_inv)
    }
}
