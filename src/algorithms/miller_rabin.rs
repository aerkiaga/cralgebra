use crate::*;

/// Miller-Rabin primality test.
///
/// Takes a candidate number `n` and a random `a` coprime to `n`.
/// If a true value is returned, the number may or
/// may not be prime. If a false value is returned,
/// the number is definitely composite.
pub fn miller_rabin<
    C,
    T: Clone + CyclicOrdZeroDyn<C> + ClosedSubDyn<C> + CenteredMulDyn<C> + OneDyn<C> + EuclidDyn<C>,
>(
    n: &T,
    a: &T,
    ctx: &C,
) -> bool {
    // TODO: checks
    if n.is_zero_d(ctx) || n.is_one_d(ctx) {
        return false;
    }
    let mc = (ModularCtx::new(n.clone(), ctx), ctx);
    let am = ModularDyn::new_d(a.clone(), &mc);
    let mut s = T::zero_d(ctx);
    let mut d = n.sub_d(&T::one_d(ctx), ctx);
    let two = T::one_d(ctx).add_d(&T::one_d(ctx), ctx);
    loop {
        let (q, r) = d.euclid_div_rem_d(&two, ctx);
        if !r.is_zero_d(ctx) {
            break;
        }
        d = q;
        s.add_assign_d(&T::one_d(ctx), ctx);
    }
    let mut x = am.pow_d(&d, &mc, ctx);
    if x.is_one_d(&mc) {
        return true;
    }
    loop {
        if x.add_d(&ModularDyn::one_d(&mc), &mc).is_zero_d(&mc) {
            return true;
        }
        if s.is_one_d(ctx) {
            return false;
        }
        x = x.mul_d(&x, &mc);
        s.sub_assign_d(&T::one_d(ctx), ctx);
    }
}

#[test]
fn miller_rabin_test() {
    let expected = [
        false, false, true, true, false, true, false, true, false, false, false, true, false, true,
        false, false, false, true, false, true, false, false, false, true, false, false, false,
        false, false, true, false, true, false, false, false, false, false, true, false, false,
        false, true, false, true, false, false, false, true, false, false, false, false, false,
        true, false, false, false, false, false, true, false, true, false, false, false, false,
        false, true, false, false, false, true, false, true, false, false, false, false, false,
        true, false, false, false, true, false, false, false, false, false, true, false, false,
        false, false, false, false, false, true, false, false,
    ];
    let a = Z2_8 { inner: 2 };
    for ni in (3..100).step_by(2) {
        let n = Z2_8 { inner: ni };
        let res = miller_rabin(&n, &a, &());
        assert_eq!(res, expected[ni as usize]);
    }
}
