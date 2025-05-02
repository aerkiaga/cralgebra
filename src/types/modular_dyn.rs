use crate::*;
use rand::{distributions::Distribution, Rng};
use std::marker::PhantomData;

/// Context for [ModularDyn].
#[derive(Clone)]
pub struct ModularContext<T, C> {
    phantom: PhantomData<C>,
    modulo: T, // the modulo for this ring
    use_barrett: bool,
    mu: T, // precomputed mu for Barrett reduction
}

impl<
        C,
        T: CyclicOrdZeroDyn<C>
            + ClosedAddDyn<C>
            + ClosedSubDyn<C>
            + ZeroDyn<C>
            + OneDyn<C>
            + EuclidDyn<C>,
    > ModularContext<T, C>
{
    /// Creates a new context from a modulo.
    ///
    /// This operation may be expensive, so
    /// contexts should be reused as much as possible.
    pub fn new(modulo: T, ctx: &C) -> Self {
        let max = T::zero_d(ctx).sub_d(&T::one_d(ctx), ctx);
        let (mut mu, mut mu_rem) = max.euclid_div_rem_d(&modulo, ctx);
        mu_rem.add_assign_d(&T::one_d(ctx), ctx);
        if !mu_rem.cyclic_lt0_d(&modulo, ctx) {
            mu.add_assign_d(&T::one_d(ctx), ctx);
        }
        let use_barrett = mu.cyclic_lt0_d(&modulo, ctx);
        Self {
            phantom: PhantomData,
            modulo,
            use_barrett,
            mu,
        }
    }
}

/// Modular integer ring with runtime modulo.
///
/// Builds modular arithmetic on top of a cyclic ring `T`.
///
/// # Notes
/// If `T` is not large enough to accomodate products
/// of any two values in the modular ring without loss
/// of information, Barrett multiplication will be used.
/// This is generally efficient, except for very small types
/// (e.g., [Z2_8]), for which using a larger type might be
/// preferable.
#[repr(transparent)]
#[derive(Clone, Eq, PartialEq)]
pub struct ModularDyn<T> {
    /// The underlying value. Avoid setting it manually.
    pub inner: T,
}

impl<T> ModularDyn<T> {
    /// A safe constructor for [ModularDyn].
    ///
    /// Will check against modulus in debug mode.
    pub fn new_d<C>(value: T, ctx: &(ModularContext<T, C>, &C)) -> Self
    where T: CyclicOrdZeroDyn<C>
    {
        let m = &ctx.0.modulo;
        let c = ctx.1;
        debug_assert!(value.cyclic_lt0_d(m, c));
        Self { inner: value }
    }
}

impl<C, T: CyclicOrdDyn<C>> CyclicOrdDyn<(ModularContext<T, C>, &C)> for ModularDyn<T> {
    fn cyclic_lt_d(&self, low: &Self, high: &Self, ctx: &(ModularContext<T, C>, &C)) -> bool {
        let c = ctx.1;
        self.inner.cyclic_lt_d(&low.inner, &high.inner, c)
    }
}

impl<C, T: CyclicOrdCostDyn<C>> CyclicOrdCostDyn<(ModularContext<T, C>, &C)> for ModularDyn<T> {
    fn cyclic_lt_cost_d(ctx: &(ModularContext<T, C>, &C)) -> f64 {
        let c = ctx.1;
        T::cyclic_lt_cost_d(c)
    }
}

impl<C, T: CyclicOrdZeroDyn<C>> CyclicOrdZeroDyn<(ModularContext<T, C>, &C)> for ModularDyn<T> {
    fn cyclic_lt0_d(&self, high: &Self, ctx: &(ModularContext<T, C>, &C)) -> bool {
        let c = ctx.1;
        self.inner.cyclic_lt0_d(&high.inner, c)
    }
}

impl<C, T: CyclicOrdZeroCostDyn<C>> CyclicOrdZeroCostDyn<(ModularContext<T, C>, &C)>
    for ModularDyn<T>
{
    fn cyclic_lt0_cost_d(ctx: &(ModularContext<T, C>, &C)) -> f64 {
        let c = ctx.1;
        T::cyclic_lt0_cost_d(c)
    }
}

impl<C, T: CyclicOrdZeroDyn<C> + ClosedAddDyn<C> + ClosedSubDyn<C>>
    ClosedAddDyn<(ModularContext<T, C>, &C)> for ModularDyn<T>
{
    fn add_d(&self, rhs: &Self, ctx: &(ModularContext<T, C>, &C)) -> Self {
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
        Self::new_d(r, ctx)
    }
}

impl<C, T: ClosedAddCostDyn<C> + CyclicOrdZeroCostDyn<C>>
    ClosedAddCostDyn<(ModularContext<T, C>, &C)> for ModularDyn<T>
{
    fn add_cost_d(ctx: &(ModularContext<T, C>, &C)) -> f64 {
        let c = ctx.1;
        T::add_cost_d(c) + 2.0 * T::cyclic_lt0_cost_d(c)
    }
}

#[test]
fn add_test() {
    use rand::rngs::mock::StepRng;
    let mut rng = StepRng::new(0, 0x54825a7f54825a7f);
    let base_dist = StandardDyn::new(&());
    for _ in 0..100 {
        let m: Z2_8 = rng.sample(&base_dist);
        if m.is_zero_d(&()) {
            continue;
        }
        let c = ModularContext::new(m.clone(), &());
        let ctx = (c, &());
        let modular_dist = StandardDyn::new(&ctx);
        let a: ModularDyn<Z2_8> = rng.sample(&modular_dist);
        let b: ModularDyn<Z2_8> = rng.sample(&modular_dist);
        let r = a.add_d(&b, &ctx);
        let expected = ((a.inner.inner as u16 + b.inner.inner as u16) % m.inner as u16) as u8;
        println!(
            "{} + {} mod {} = {}",
            a.inner.inner, b.inner.inner, m.inner, expected
        );
        assert_eq!(r.inner.inner, expected);
    }
}

impl<C, T: CyclicOrdZeroDyn<C> + ClosedAddDyn<C> + ClosedSubDyn<C>>
    ClosedSubDyn<(ModularContext<T, C>, &C)> for ModularDyn<T>
{
    fn sub_d(&self, rhs: &Self, ctx: &(ModularContext<T, C>, &C)) -> Self {
        let m = &ctx.0.modulo;
        let c = ctx.1;
        let diff = self.inner.sub_d(&rhs.inner, c);
        let r = if self.inner.cyclic_lt0_d(&diff, c) {
            diff.add_d(m, c)
        } else {
            diff
        };
        Self::new_d(r, ctx)
    }
}

impl<C, T: ClosedSubCostDyn<C> + CyclicOrdZeroCostDyn<C>>
    ClosedSubCostDyn<(ModularContext<T, C>, &C)> for ModularDyn<T>
{
    fn sub_cost_d(ctx: &(ModularContext<T, C>, &C)) -> f64 {
        let c = ctx.1;
        T::sub_cost_d(c) + 1.0 * T::cyclic_lt0_cost_d(c)
    }
}

#[test]
fn sub_test() {
    use rand::rngs::mock::StepRng;
    let mut rng = StepRng::new(0, 0x54825a7f54825a7f);
    let base_dist = StandardDyn::new(&());
    for _ in 0..100 {
        let m: Z2_8 = rng.sample(&base_dist);
        if m.is_zero_d(&()) {
            continue;
        }
        let c = ModularContext::new(m.clone(), &());
        let ctx = (c, &());
        let modular_dist = StandardDyn::new(&ctx);
        let a: ModularDyn<Z2_8> = rng.sample(&modular_dist);
        let b: ModularDyn<Z2_8> = rng.sample(&modular_dist);
        let r = a.sub_d(&b, &ctx);
        let expected =
            ((a.inner.inner as u16 + m.inner as u16 - b.inner.inner as u16) % m.inner as u16) as u8;
        println!(
            "{} - {} mod {} = {}",
            a.inner.inner, b.inner.inner, m.inner, expected
        );
        assert_eq!(r.inner.inner, expected);
    }
}

impl<C, T: CyclicOrdZeroDyn<C> + ZeroDyn<C>> ZeroDyn<(ModularContext<T, C>, &C)> for ModularDyn<T> {
    fn zero_d(ctx: &(ModularContext<T, C>, &C)) -> Self {
        let c = ctx.1;
        Self::new_d(T::zero_d(c), ctx)
    }
}

impl<
        C,
        T: CyclicOrdZeroDyn<C>
            + ClosedSubDyn<C>
            + ZeroDyn<C>
            + CenteredMulDyn<C>
            + OneDyn<C>
            + EuclidDyn<C>,
    > ClosedMulDyn<(ModularContext<T, C>, &C)> for ModularDyn<T>
{
    fn mul_d(&self, rhs: &Self, ctx: &(ModularContext<T, C>, &C)) -> Self {
        let m = &ctx.0.modulo;
        let c = ctx.1;
        Self::new_d(
            if !&ctx.0.use_barrett {
                self.inner.mul_d(&rhs.inner, c).euclid_rem_d(m, c)
            } else {
                let mu = &ctx.0.mu;
                let (mut low, mut high) = self.inner.widening_mul_d(&rhs.inner, c);
                // Barrett reduction
                while !high.is_zero_d(c) {
                    let mut q_high = high.mul_d(mu, c);
                    q_high.add_assign_d(&low.centered_mul_d(mu, c), c);
                    let (q_m_low, q_m_high) = q_high.widening_mul_d(m, c);
                    let r_low = low.sub_d(&q_m_low, c);
                    let mut r_high = high.sub_d(&q_m_high, c);
                    if low.cyclic_lt0_d(&q_m_low, c) {
                        r_high.sub_assign_d(&T::one_d(c), c);
                    }
                    low = r_low;
                    high = r_high;
                }
                low.euclid_rem_d(m, c)
            },
            ctx,
        )
    }
}

impl<
        C,
        T: ClosedMulCostDyn<C>
            + CenteredMulCostDyn<C>
            + ClosedAddCostDyn<C>
            + ClosedSubCostDyn<C>
            + CyclicOrdZeroCostDyn<C>
            + EuclidCostDyn<C>,
    > ClosedMulCostDyn<(ModularContext<T, C>, &C)> for ModularDyn<T>
{
    fn mul_cost_d(ctx: &(ModularContext<T, C>, &C)) -> f64 {
        let c = ctx.1;
        if !&ctx.0.use_barrett {
            T::mul_cost_d(c) + T::euclid_cost_d(c) - 1.0
        } else {
            T::centered_mul_cost_d(c)
                + 1.0
                    * (2.0 * T::centered_mul_cost_d(c)
                        + T::mul_cost_d(c)
                        + 3.0 * T::sub_cost_d(c)
                        + T::cyclic_lt0_cost_d(c))
                + T::euclid_cost_d(c)
        }
    }
}

#[test]
fn mul_test() {
    use rand::rngs::mock::StepRng;
    let mut rng = StepRng::new(0, 0x54825a7f54825a7f);
    let base_dist = StandardDyn::new(&());
    for _ in 0..100 {
        let m: Z2_8 = rng.sample(&base_dist);
        if m.is_zero_d(&()) {
            continue;
        }
        let c = ModularContext::new(m.clone(), &());
        let ctx = (c, &());
        let modular_dist = StandardDyn::new(&ctx);
        let a: ModularDyn<Z2_8> = rng.sample(&modular_dist);
        let b: ModularDyn<Z2_8> = rng.sample(&modular_dist);
        let r = a.mul_d(&b, &ctx);
        let expected = ((a.inner.inner as u16 * b.inner.inner as u16) % m.inner as u16) as u8;
        println!(
            "{} * {} mod {} = {}",
            a.inner.inner, b.inner.inner, m.inner, expected,
        );
        assert_eq!(r.inner.inner, expected);
    }
}

impl<C, T: CyclicOrdZeroDyn<C> + OneDyn<C>> OneDyn<(ModularContext<T, C>, &C)> for ModularDyn<T> {
    fn one_d(ctx: &(ModularContext<T, C>, &C)) -> Self {
        let c = ctx.1;
        Self::new_d(T::one_d(c), ctx)
    }
}

impl<C, D, T, Rhs: ClosedAddDyn<D> + ClosedSubDyn<D> + ZeroDyn<D> + OneDyn<D> + EuclidDyn<D>> PowDyn<C, D, Rhs>
    for ModularDyn<T>
where
    Self: Clone + ClosedMulDyn<C> + OneDyn<C>,
{
}

impl<C, D, T, Rhs: ClosedAddDyn<D> + ClosedSubDyn<D> + ZeroDyn<D> + OneDyn<D> + EuclidDyn<D>
    > PowCostDyn<C, D, Rhs> for ModularDyn<T>
    where
    Self: ClosedMulCostDyn<C>
{
    
}

impl<C, T: CyclicOrdZeroDyn<C> + ClosedAddDyn<C> + ClosedMulDyn<C> + OneDyn<C> + EuclidDyn<C>>
    Distribution<ModularDyn<T>> for StandardDyn<'_, (ModularContext<T, C>, &C)>
where
    for<'a> StandardDyn<'a, C>: Distribution<T>,
{
    fn sample<R: ?Sized + Rng>(&self, rng: &mut R) -> ModularDyn<T> {
        let m = &self.ctx.0.modulo;
        let c = self.ctx.1;
        let dist = StandardDyn::new(c);
        loop {
            let x: T = rng.sample(&dist);
            let (q, r) = x.euclid_div_rem_d(m, c);
            let prod = q.mul_d(&m.add_d(&T::one_d(c), c), c);
            if !prod.cyclic_lt0_d(m, c) {
                return ModularDyn { inner: r };
            }
        }
    }
}
