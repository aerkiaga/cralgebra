#![feature(bigint_helper_methods)]

pub mod algorithms;
//pub(crate) use algorithms::*;
pub mod ops;
pub(crate) use ops::*;
pub mod types;
pub(crate) use types::*;
pub mod misc;
pub(crate) use misc::*;

#[test]
pub fn readme_test() {
    let modulus: Z2_8 = 17.into();
    let inner_ctx = (); // Z2_8 takes no context
    let mod_ctx = ModularContext::new(modulus.clone(), &inner_ctx);
    let ctx = (mod_ctx, &inner_ctx); // this is how contexts are nested
    let a: ModularDyn<Z2_8> = ModularDyn::new_d(4.into(), &ctx);
    let b: ModularDyn<Z2_8> = ModularDyn::new_d(15.into(), &ctx);
    let r = a.add_d(&b, &ctx);
    assert_eq!(r.inner.inner, 2);
}
