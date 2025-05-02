use cralgebra::{algorithms::*, misc::*, ops::*, types::*};
use rand::{distributions::Distribution, rngs::mock::StepRng, Rng};
use std::hint::black_box;
use std::time::Instant;

fn bench_add<'a, C: 'a, T: ClosedAddDyn<C>>(name: &str, ctx: &'a C)
where
    StandardDyn<'a, C>: Distribution<T>,
{
    let mut rng = StepRng::new(0, 0x1234567898765431);
    let dist = StandardDyn::new(ctx);
    let mut a = black_box(rng.sample(&dist));
    let mut b: [T; 10] = black_box(std::array::from_fn(|_| black_box(rng.sample(&dist))));
    let t = Instant::now();
    for _ in 0..100 {
        a.add_assign_d(&b[0], ctx);
        a.add_assign_d(&b[1], ctx);
        a.add_assign_d(&b[2], ctx);
        a.add_assign_d(&b[3], ctx);
        a.add_assign_d(&b[4], ctx);
        a.add_assign_d(&b[5], ctx);
        a.add_assign_d(&b[6], ctx);
        a.add_assign_d(&b[7], ctx);
        a.add_assign_d(&b[8], ctx);
        a.add_assign_d(&b[9], ctx);
        a = black_box(a);
        b = black_box(b);
    }
    black_box(a);
    let cost = t.elapsed().div_f64(1000.0);
    let expected = T::add_cost_d(ctx);
    println!("{name:.<40} {cost:9.1?} {expected:<10.0}");
}

fn bench_mul<'a, C: 'a, T: ClosedMulDyn<C>>(name: &str, ctx: &'a C)
where
    StandardDyn<'a, C>: Distribution<T>,
{
    let mut rng = StepRng::new(0, 0x1234567898765431);
    let dist = StandardDyn::new(ctx);
    let mut a = black_box(rng.sample(&dist));
    let mut b: [T; 10] = black_box(std::array::from_fn(|_| black_box(rng.sample(&dist))));
    let t = Instant::now();
    for _ in 0..100 {
        a.mul_assign_d(&b[0], ctx);
        a.mul_assign_d(&b[1], ctx);
        a.mul_assign_d(&b[2], ctx);
        a.mul_assign_d(&b[3], ctx);
        a.mul_assign_d(&b[4], ctx);
        a.mul_assign_d(&b[5], ctx);
        a.mul_assign_d(&b[6], ctx);
        a.mul_assign_d(&b[7], ctx);
        a.mul_assign_d(&b[8], ctx);
        a.mul_assign_d(&b[9], ctx);
        a = black_box(a);
        b = black_box(b);
    }
    black_box(a);
    let cost = t.elapsed().div_f64(1000.0);
    let expected = T::mul_cost_d(ctx);
    println!("{name:.<40} {cost:9.1?} {expected:<10.0}");
}

fn bench_closure<'a, C: 'a, W, T, F: Fn(&T, &T, &'a C) -> W, G: Fn(&'a C) -> f64>(
    name: &str,
    f: F,
    g: G,
    ctx: &'a C,
) where
    StandardDyn<'a, C>: Distribution<T>,
{
    let mut rng = StepRng::new(0, 0x1234567898765431);
    let dist = StandardDyn::new(ctx);
    let mut b: [(T, T); 10] = black_box(std::array::from_fn(|_| {
        black_box((rng.sample(&dist), rng.sample(&dist)))
    }));
    let t = Instant::now();
    for _ in 0..100 {
        black_box(f(&b[0].0, &b[0].1, ctx));
        black_box(f(&b[1].0, &b[1].1, ctx));
        black_box(f(&b[2].0, &b[2].1, ctx));
        black_box(f(&b[3].0, &b[3].1, ctx));
        black_box(f(&b[4].0, &b[4].1, ctx));
        black_box(f(&b[5].0, &b[5].1, ctx));
        black_box(f(&b[6].0, &b[6].1, ctx));
        black_box(f(&b[7].0, &b[7].1, ctx));
        black_box(f(&b[8].0, &b[8].1, ctx));
        black_box(f(&b[9].0, &b[9].1, ctx));
        b = black_box(b);
    }
    let cost = t.elapsed().div_f64(1000.0);
    let expected = g(ctx);
    println!("{name:.<40} {cost:9.1?} {expected:<10.0}");
}

fn main() {
	println!("\nClosedAddDyn");
    bench_add::<_, Z2_8>("Z2_8", &());
    bench_add::<_, Z2_16>("Z2_16", &());
    bench_add::<_, Z2_32>("Z2_32", &());
    bench_add::<_, Z2_64>("Z2_64", &());
    bench_add::<_, Z2_128>("Z2_128", &());
    
    bench_add::<_, ModularDyn<Z2_8>>(
        "ModularDyn<Z2_8>",
        &(ModularContext::new(Z2_8::one_d(&()), &()), &()),
    );
    bench_add::<_, ModularDyn<Z2_16>>(
        "ModularDyn<Z2_16>",
        &(ModularContext::new(Z2_16::one_d(&()), &()), &()),
    );
    bench_add::<_, ModularDyn<Z2_32>>(
        "ModularDyn<Z2_32>",
        &(ModularContext::new(Z2_32::one_d(&()), &()), &()),
    );
    bench_add::<_, ModularDyn<Z2_64>>(
        "ModularDyn<Z2_64>",
        &(ModularContext::new(Z2_64::one_d(&()), &()), &()),
    );
    bench_add::<_, ModularDyn<Z2_128>>(
        "ModularDyn<Z2_128>",
        &(ModularContext::new(Z2_128::one_d(&()), &()), &()),
    );
    
    bench_add::<_, MontgomeryDyn<Z2_8>>(
        "MontgomeryDyn<Z2_8>",
        &(MontgomeryContext::new(Z2_8::one_d(&()), &()), &()),
    );
    bench_add::<_, MontgomeryDyn<Z2_16>>(
        "MontgomeryDyn<Z2_16>",
        &(MontgomeryContext::new(Z2_16::one_d(&()), &()), &()),
    );
    bench_add::<_, MontgomeryDyn<Z2_32>>(
        "MontgomeryDyn<Z2_32>",
        &(MontgomeryContext::new(Z2_32::one_d(&()), &()), &()),
    );
    bench_add::<_, MontgomeryDyn<Z2_64>>(
        "MontgomeryDyn<Z2_64>",
        &(MontgomeryContext::new(Z2_64::one_d(&()), &()), &()),
    );
    bench_add::<_, MontgomeryDyn<Z2_128>>(
        "MontgomeryDyn<Z2_128>",
        &(MontgomeryContext::new(Z2_128::one_d(&()), &()), &()),
    );
    
	println!("\nClosedMulDyn");
    bench_mul::<_, Z2_8>("Z2_8", &());
    bench_mul::<_, Z2_16>("Z2_16", &());
    bench_mul::<_, Z2_32>("Z2_32", &());
    bench_mul::<_, Z2_64>("Z2_64", &());
    bench_mul::<_, Z2_128>("Z2_128", &());
    
    bench_mul::<_, ModularDyn<Z2_8>>(
        "ModularDyn<Z2_8> (L)",
        &(ModularContext::new(Z2_8 { inner: 10 }, &()), &()),
    );
    bench_mul::<_, ModularDyn<Z2_8>>(
        "ModularDyn<Z2_8> (B)",
        &(ModularContext::new(Z2_8 { inner: 1 << 6 }, &()), &()),
    );
    bench_mul::<_, ModularDyn<Z2_16>>(
        "ModularDyn<Z2_16> (L)",
        &(ModularContext::new(Z2_16 { inner: 10 }, &()), &()),
    );
    bench_mul::<_, ModularDyn<Z2_16>>(
        "ModularDyn<Z2_16> (B)",
        &(ModularContext::new(Z2_16 { inner: 1 << 10 }, &()), &()),
    );
    bench_mul::<_, ModularDyn<Z2_32>>(
        "ModularDyn<Z2_32> (L)",
        &(ModularContext::new(Z2_32 { inner: 10 }, &()), &()),
    );
    bench_mul::<_, ModularDyn<Z2_32>>(
        "ModularDyn<Z2_32> (B)",
        &(ModularContext::new(Z2_32 { inner: 1 << 18 }, &()), &()),
    );
    bench_mul::<_, ModularDyn<Z2_64>>(
        "ModularDyn<Z2_64> (L)",
        &(ModularContext::new(Z2_64 { inner: 10 }, &()), &()),
    );
    bench_mul::<_, ModularDyn<Z2_64>>(
        "ModularDyn<Z2_64> (B)",
        &(ModularContext::new(Z2_64 { inner: 1 << 34 }, &()), &()),
    );
    bench_mul::<_, ModularDyn<Z2_128>>(
        "ModularDyn<Z2_128> (L)",
        &(ModularContext::new(Z2_128 { inner: 10 }, &()), &()),
    );
    bench_mul::<_, ModularDyn<Z2_128>>(
        "ModularDyn<Z2_128> (B)",
        &(ModularContext::new(Z2_128 { inner: 1 << 66 }, &()), &()),
    );
    
    bench_mul::<_, MontgomeryDyn<Z2_8>>(
        "MontgomeryDyn<Z2_8>",
        &(MontgomeryContext::new(Z2_8{inner: 100,}, &()), &()),
    );
    bench_mul::<_, MontgomeryDyn<Z2_16>>(
        "MontgomeryDyn<Z2_16>",
        &(MontgomeryContext::new(Z2_16{inner: 10000,}, &()), &()),
    );
    bench_mul::<_, MontgomeryDyn<Z2_32>>(
        "MontgomeryDyn<Z2_32>",
        &(MontgomeryContext::new(Z2_32{inner: 100000000,}, &()), &()),
    );
    bench_mul::<_, MontgomeryDyn<Z2_64>>(
        "MontgomeryDyn<Z2_64>",
        &(MontgomeryContext::new(Z2_64{inner: 10000000000000000,}, &()), &()),
    );
    bench_mul::<_, MontgomeryDyn<Z2_128>>(
        "MontgomeryDyn<Z2_128>",
        &(MontgomeryContext::new(Z2_128{inner: 100000000000000000000000000000000,}, &()), &()),
    );
    
    println!("\nPowDyn");
    bench_closure(
        "ModularDyn<Z2_8> (2)",
        |a: &ModularDyn<Z2_8>, _, ctx| a.pow_d(&Z2_8 { inner: 100 }, ctx, &()),
        |ctx| <ModularDyn<_> as PowCostDyn::<_, _, Z2_8>>::pow_cost_d(ctx, &()),
        &(ModularContext::new(Z2_8 { inner: 1 << 6 }, &()), &()),
    );
    bench_closure(
        "ModularDyn<Z2_8> (38)",
        |a: &ModularDyn<Z2_8>, _, ctx| {
            a.pow_d(
                &Z2_128 {
                    inner: 100000000000000000000000000000000000000,
                },
                ctx,
                &(),
            )
        },
        |ctx| <ModularDyn<_> as PowCostDyn::<_, _, Z2_128>>::pow_cost_d(ctx, &()),
        &(ModularContext::new(Z2_8 { inner: 1 << 6 }, &()), &()),
    );
    bench_closure(
        "ModularDyn<Z2_128> (2)",
        |a: &ModularDyn<Z2_128>, _, ctx| a.pow_d(&Z2_8 { inner: 100 }, ctx, &()),
       |ctx| <ModularDyn<_> as PowCostDyn::<_, _, Z2_8>>::pow_cost_d(ctx, &()),
        &(ModularContext::new(Z2_128 { inner: 1 << 66 }, &()), &()),
    );
    bench_closure(
        "ModularDyn<Z2_128> (38)",
        |a: &ModularDyn<Z2_128>, _, ctx| {
            a.pow_d(
                &Z2_128 {
                    inner: 100000000000000000000000000000000000000,
                },
                ctx,
                &(),
            )
        },
        |ctx| <ModularDyn<_> as PowCostDyn::<_, _, Z2_128>>::pow_cost_d(ctx, &()),
        &(ModularContext::new(Z2_128 { inner: 1 << 66 }, &()), &()),
    );
    
    bench_closure(
        "MontgomeryDyn<Z2_8> (2)",
        |a: &MontgomeryDyn<Z2_8>, _, ctx| a.pow_d(&Z2_8 { inner: 100 }, ctx, &()),
        |ctx| <MontgomeryDyn<_> as PowCostDyn::<_, _, Z2_8>>::pow_cost_d(ctx, &()),
        &(MontgomeryContext::new(Z2_8 { inner: 1 << 6 }, &()), &()),
    );
    bench_closure(
        "MontgomeryDyn<Z2_8> (38)",
        |a: &MontgomeryDyn<Z2_8>, _, ctx| {
            a.pow_d(
                &Z2_128 {
                    inner: 100000000000000000000000000000000000000,
                },
                ctx,
                &(),
            )
        },
        |ctx| <MontgomeryDyn<_> as PowCostDyn::<_, _, Z2_128>>::pow_cost_d(ctx, &()),
        &(MontgomeryContext::new(Z2_8 { inner: 1 << 6 }, &()), &()),
    );
    bench_closure(
        "MontgomeryDyn<Z2_128> (2)",
        |a: &MontgomeryDyn<Z2_128>, _, ctx| a.pow_d(&Z2_8 { inner: 100 }, ctx, &()),
        |ctx| <MontgomeryDyn<_> as PowCostDyn::<_, _, Z2_8>>::pow_cost_d(ctx, &()),
        &(MontgomeryContext::new(Z2_128 { inner: 1 << 66 }, &()), &()),
    );
    bench_closure(
        "MontgomeryDyn<Z2_128> (38)",
        |a: &MontgomeryDyn<Z2_128>, _, ctx| {
            a.pow_d(
                &Z2_128 {
                    inner: 100000000000000000000000000000000000000,
                },
                ctx,
                &(),
            )
        },
        |ctx| <MontgomeryDyn<_> as PowCostDyn::<_, _, Z2_128>>::pow_cost_d(ctx, &()),
        &(MontgomeryContext::new(Z2_128 { inner: 1 << 66 }, &()), &()),
    );
    
    println!("\nInvDyn");
    bench_closure(
        "Z2_8",
        |n: &Z2_8, _, ctx| n.inv_d(ctx),
        |ctx| 0.0,
        &(),
    );
    bench_closure(
        "Z2_16",
        |n: &Z2_16, _, ctx| n.inv_d(ctx),
        |ctx| 0.0,
        &(),
    );
    bench_closure(
        "Z2_32",
        |n: &Z2_32, _, ctx| n.inv_d(ctx),
        |ctx| 0.0,
        &(),
    );
    bench_closure(
        "Z2_64",
        |n: &Z2_64, _, ctx| n.inv_d(ctx),
        |ctx| 0.0,
        &(),
    );
    bench_closure(
        "Z2_128",
        |n: &Z2_128, _, ctx| n.inv_d(ctx),
        |ctx| 0.0,
        &(),
    );

	println!("\nnew");
	bench_closure(
        "ModularContext<Z2_8, _>",
        |a: &Z2_8, _, ctx| ModularContext::new(Z2_8 {inner: a.inner | 1,}, ctx),
        |ctx| 0.0,
        &(),
    );
    bench_closure(
        "ModularContext<Z2_16, _>",
        |a: &Z2_16, _, ctx| ModularContext::new(Z2_16 {inner: a.inner | 1,}, ctx),
        |ctx| 0.0,
        &(),
    );
    bench_closure(
        "ModularContext<Z2_32, _>",
        |a: &Z2_32, _, ctx| ModularContext::new(Z2_32 {inner: a.inner | 1,}, ctx),
        |ctx| 0.0,
        &(),
    );
    bench_closure(
        "ModularContext<Z2_64, _>",
        |a: &Z2_64, _, ctx| ModularContext::new(Z2_64 {inner: a.inner | 1,}, ctx),
        |ctx| 0.0,
        &(),
    );
    bench_closure(
        "ModularContext<Z2_128, _>",
        |a: &Z2_128, _, ctx| ModularContext::new(Z2_128 {inner: a.inner | 1,}, ctx),
        |ctx| 0.0,
        &(),
    );
    
	bench_closure(
        "MontgomeryContext<Z2_8, _>",
        |a: &Z2_8, _, ctx| MontgomeryContext::new(Z2_8 {inner: a.inner | 1,}, ctx),
        |ctx| 0.0,
        &(),
    );
    bench_closure(
        "MontgomeryContext<Z2_16, _>",
        |a: &Z2_16, _, ctx| MontgomeryContext::new(Z2_16 {inner: a.inner | 1,}, ctx),
        |ctx| 0.0,
        &(),
    );
    bench_closure(
        "MontgomeryContext<Z2_32, _>",
        |a: &Z2_32, _, ctx| MontgomeryContext::new(Z2_32 {inner: a.inner | 1,}, ctx),
        |ctx| 0.0,
        &(),
    );
    bench_closure(
        "MontgomeryContext<Z2_64, _>",
        |a: &Z2_64, _, ctx| MontgomeryContext::new(Z2_64 {inner: a.inner | 1,}, ctx),
        |ctx| 0.0,
        &(),
    );
    bench_closure(
        "MontgomeryContext<Z2_128, _>",
        |a: &Z2_128, _, ctx| MontgomeryContext::new(Z2_128 {inner: a.inner | 1,}, ctx),
        |ctx| 0.0,
        &(),
    );
    
    println!("\nmiller_rabin");
    bench_closure(
        "Z2_8",
        |n: &Z2_8, _, ctx| miller_rabin(n, &n.sub_d(&Z2_8::one_d(ctx), ctx), ctx),
        |ctx| 0.0,
        &(),
    );
    bench_closure(
        "Z2_16",
        |n: &Z2_16, _, ctx| miller_rabin(n, &n.sub_d(&Z2_16::one_d(ctx), ctx), ctx),
        |ctx| 0.0,
        &(),
    );
    bench_closure(
        "Z2_32",
        |n: &Z2_32, _, ctx| miller_rabin(n, &n.sub_d(&Z2_32::one_d(ctx), ctx), ctx),
        |ctx| 0.0,
        &(),
    );
    bench_closure(
        "Z2_64",
        |n: &Z2_64, _, ctx| miller_rabin(n, &n.sub_d(&Z2_64::one_d(ctx), ctx), ctx),
        |ctx| 0.0,
        &(),
    );
    bench_closure(
        "Z2_128",
        |n: &Z2_128, _, ctx| miller_rabin(n, &n.sub_d(&Z2_128::one_d(ctx), ctx), ctx),
        |ctx| 0.0,
        &(),
    );
}
