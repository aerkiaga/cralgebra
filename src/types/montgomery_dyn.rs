use crate::*;
use rand::{Rng, distributions::Distribution};
use std::marker::PhantomData;

/// Context for [MontgomeryDyn].
pub struct MontgomeryContext<T, C> {
    phantom: PhantomData<C>,
    modulo: T,             // the modulo for this ring
    one: MontgomeryDyn<T>, // r % modulo (1 in Montgomery form)
    r2: MontgomeryDyn<T>,  // r² % modulo (r % modulo in Montgomery form)
    m_inv: T,              // modulo⁻¹ % r
}

impl<
    'a,
    C: 'a,
    T: Clone
        + ClosedSubDyn<C>
        + ZeroDyn<C>
        + InvDyn<C>
        + EuclidDyn<C>
        + OrderDyn<C, (MontgomeryContext<T, C>, &'a C), MontgomeryDyn<T>>,
> MontgomeryContext<T, C>
{
    /// Creates a new context from a modulo.
    ///
    /// This operation may be expensive, so
    /// contexts should be reused as much as possible.
    pub fn new(modulo: T, ctx: &'a C) -> Self {
        let m_inv = modulo.inv_d(ctx);
        let one = MontgomeryDyn {
            inner: T::zero_d(ctx)
                .sub_d(&modulo, ctx)
                .euclid_rem_d(&modulo, ctx),
        };
        let dummy_context = MontgomeryContext {
            phantom: PhantomData,
            modulo: modulo.clone(),
            one: one.clone(),
            r2: MontgomeryDyn {
                inner: modulo.clone(),
            },
            m_inv: m_inv.clone(),
        };
        let mc = (dummy_context, ctx);
        let r2: MontgomeryDyn<T> = T::order_d(ctx, &mc);
        Self {
            phantom: PhantomData,
            modulo,
            one,
            r2,
            m_inv,
        }
    }
}

/// Modular integer ring in Montgomery form, with runtime modulo.
#[repr(transparent)]
#[derive(Clone, Eq, PartialEq)]
pub struct MontgomeryDyn<T> {
    inner: T,
}

impl<T> MontgomeryDyn<T> {
    pub fn new_d<C>(value: T, ctx: &(MontgomeryContext<T, C>, &C)) -> Self
    where
        T: CyclicOrdZeroDyn<C> + ClosedAddDyn<C> + ClosedSubDyn<C> + CenteredMulDyn<C>,
    {
        let r2 = &ctx.0.r2;
        let c = ctx.1;
        Self { inner: value }.mul_d(r2, ctx)
    }
}

impl<T> MontgomeryDyn<T> {
    pub fn inner_d<C>(&self, ctx: &(MontgomeryContext<T, C>, &C)) -> T
    where
        T: ZeroDyn<C> + ClosedSubDyn<C> + ClosedMulDyn<C> + CenteredMulDyn<C>,
    {
        let m = &ctx.0.modulo;
        let m_inv = &ctx.0.m_inv;
        let c = ctx.1;
        let q = self.inner.mul_d(m_inv, c);
        let w = q.centered_mul_d(m, c);
        if w.is_zero_d(c) {
            T::zero_d(c)
        } else {
            m.sub_d(&w, c)
        }
    }
}

impl<C, T: CyclicOrdZeroDyn<C> + ClosedAddDyn<C> + ClosedSubDyn<C>>
    ClosedAddDyn<(MontgomeryContext<T, C>, &C)> for MontgomeryDyn<T>
{
    fn add_d(&self, rhs: &Self, ctx: &(MontgomeryContext<T, C>, &C)) -> Self {
        let m = &ctx.0.modulo;
        let c = ctx.1;
        let sum = self.inner.add_d(&rhs.inner, c);
        let r = if !sum.cyclic_lt0_d(m, c)
            || sum.cyclic_lt0_d(&self.inner, c)
            || sum.cyclic_lt0_d(&rhs.inner, c)
        {
            sum.sub_d(m, c)
        } else {
            sum
        };
        Self { inner: r }
    }
}

#[test]
fn new_test() {
    use rand::rngs::mock::StepRng;
    let mut rng = StepRng::new(0, 0x54825a7f54825a7f);
    let base_dist = StandardDyn::new(&());
    for _ in 0..100 {
        let mut m: Z2_8 = rng.sample(&base_dist);
        m.inner |= 1;
        let c = MontgomeryContext::new(m.clone(), &());
        let ctx = (c, &());
        let mut x_inner: Z2_8 = rng.sample(&base_dist);
        x_inner = x_inner.euclid_rem_d(&m, &());
        let x: MontgomeryDyn<Z2_8> = MontgomeryDyn::new_d(x_inner.clone(), &ctx);
        let expected = x.inner_d(&ctx).inner as u8;
        println!("{} mod {} = {}", x_inner.inner, m.inner, expected);
        assert_eq!(x_inner.inner, expected);
    }
}

#[test]
fn add_test() {
    use rand::rngs::mock::StepRng;
    let mut rng = StepRng::new(0, 0x54825a7f54825a7f);
    let base_dist = StandardDyn::new(&());
    for _ in 0..100 {
        let mut m: Z2_8 = rng.sample(&base_dist);
        m.inner |= 1;
        let c = MontgomeryContext::new(m.clone(), &());
        let ctx = (c, &());
        let montgomery_dist = StandardDyn::new(&ctx);
        let a: MontgomeryDyn<Z2_8> = rng.sample(&montgomery_dist);
        let b: MontgomeryDyn<Z2_8> = rng.sample(&montgomery_dist);
        let r = a.add_d(&b, &ctx);
        let expected =
            ((a.inner_d(&ctx).inner as u16 + b.inner_d(&ctx).inner as u16) % m.inner as u16) as u8;
        println!(
            "{} + {} mod {} = {}",
            a.inner_d(&ctx).inner,
            b.inner_d(&ctx).inner,
            m.inner,
            expected
        );
        assert_eq!(r.inner_d(&ctx).inner, expected);
    }
}

impl<C, T: CyclicOrdZeroDyn<C> + ZeroDyn<C>> ZeroDyn<(MontgomeryContext<T, C>, &C)>
    for MontgomeryDyn<T>
{
    fn zero_d(ctx: &(MontgomeryContext<T, C>, &C)) -> Self {
        let c = ctx.1;
        Self {
            inner: T::zero_d(c),
        }
    }
}

impl<C, T: CyclicOrdZeroDyn<C> + ClosedAddDyn<C> + ClosedSubDyn<C> + CenteredMulDyn<C>>
    ClosedMulDyn<(MontgomeryContext<T, C>, &C)> for MontgomeryDyn<T>
{
    fn mul_d(&self, rhs: &Self, ctx: &(MontgomeryContext<T, C>, &C)) -> Self {
        let m = &ctx.0.modulo;
        let m_inv = &ctx.0.m_inv;
        let c = ctx.1;
        let (low, high) = self.inner.widening_mul_d(&rhs.inner, c);
        let q = low.mul_d(m_inv, c);
        let w = q.centered_mul_d(m, c);
        let a = high.sub_d(&w, c);
        let r = if high.cyclic_lt0_d(&w, c) {
            a.add_d(m, c)
        } else {
            a
        };
        Self { inner: r }
    }
}

#[test]
fn mul_test() {
    use rand::rngs::mock::StepRng;
    let mut rng = StepRng::new(0, 0x54825a7f54825a7f);
    let base_dist = StandardDyn::new(&());
    for _ in 0..100 {
        let mut m: Z2_8 = rng.sample(&base_dist);
        m.inner |= 1;
        if m.inner == 255 {
            continue;
        }
        let c = MontgomeryContext::new(m.clone(), &());
        let ctx = (c, &());
        let montgomery_dist = StandardDyn::new(&ctx);
        let a: MontgomeryDyn<Z2_8> = rng.sample(&montgomery_dist);
        let b: MontgomeryDyn<Z2_8> = rng.sample(&montgomery_dist);
        let r = a.mul_d(&b, &ctx);
        let expected =
            ((a.inner_d(&ctx).inner as u16 * b.inner_d(&ctx).inner as u16) % m.inner as u16) as u8;
        println!(
            "{} * {} mod {} = {}",
            a.inner_d(&ctx).inner,
            b.inner_d(&ctx).inner,
            m.inner,
            expected,
        );
        assert_eq!(r.inner_d(&ctx).inner, expected);
    }
}

impl<C, T: Clone + CyclicOrdZeroDyn<C>> OneDyn<(MontgomeryContext<T, C>, &C)> for MontgomeryDyn<T> {
    fn one_d(ctx: &(MontgomeryContext<T, C>, &C)) -> Self {
        ctx.0.one.clone()
    }
}

impl<C, D, T, Rhs: ClosedAddDyn<D> + ClosedSubDyn<D> + ZeroDyn<D> + OneDyn<D> + EuclidDyn<D>>
    PowDyn<C, D, Rhs> for MontgomeryDyn<T>
where
    Self: Clone + ClosedMulDyn<C> + OneDyn<C>,
{
}

impl<C, T: CyclicOrdZeroDyn<C> + ClosedAddDyn<C> + ClosedMulDyn<C> + EuclidDyn<C>>
    Distribution<MontgomeryDyn<T>> for StandardDyn<'_, (MontgomeryContext<T, C>, &C)>
where
    for<'a> StandardDyn<'a, C>: Distribution<T>,
{
    fn sample<R: ?Sized + Rng>(&self, rng: &mut R) -> MontgomeryDyn<T> {
        let m = &self.ctx.0.modulo;
        let c = self.ctx.1;
        let dist = StandardDyn::new(c);
        loop {
            let x: T = rng.sample(&dist);
            let (q, r) = x.euclid_div_rem_d(m, c);
            let prod = q.mul_d(&m, c).add_d(&m, c);
            if !prod.cyclic_lt0_d(m, c) {
                return MontgomeryDyn { inner: r };
            }
        }
    }
}
