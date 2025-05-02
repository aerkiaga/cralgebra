#[cfg(test)]
extern crate test;

use std::ops::Add;

#[const_trait]
pub trait AddCost<Rhs = Self>: Add<Rhs> {
    fn add_cost() -> f64;
}

#[bench]
fn add_u64_bench(bencher: &mut test::Bencher) {
    let a = test::black_box(0x1234567887654321_u64);
    let b = test::black_box(0x9876543223456789_u64);
    bencher.iter(|| test::black_box(a + b));
}

impl const AddCost<u8> for u8 {
    fn add_cost() -> f64 {
        0.5
    }
}

impl const AddCost<u16> for u16 {
    fn add_cost() -> f64 {
        0.5
    }
}

impl const AddCost<u32> for u32 {
    fn add_cost() -> f64 {
        1.0
    }
}

impl const AddCost<u64> for u64 {
    fn add_cost() -> f64 {
        0.5
    }
}

#[bench]
fn add_u128_bench(bencher: &mut test::Bencher) {
    let a = test::black_box(0x12345678876543219876543223456789_u128);
    let b = test::black_box(0x98765432234567891234567887654321_u128);
    bencher.iter(|| test::black_box(a + b));
}

impl const AddCost<u128> for u128 {
    fn add_cost() -> f64 {
        7.0
    }
}

use std::ops::Mul;

#[const_trait]
pub trait MulCost<Rhs = Self>: Mul<Rhs> {
    fn mul_cost() -> f64;
}

#[bench]
fn mul_u64_bench(bencher: &mut test::Bencher) {
    let a = test::black_box(0x1234567887654321_u64);
    let b = test::black_box(0x9876543223456789_u64);
    bencher.iter(|| test::black_box(a.wrapping_mul(b)));
}

impl const MulCost<u8> for u8 {
    fn mul_cost() -> f64 {
        1.0
    }
}

impl const MulCost<u16> for u16 {
    fn mul_cost() -> f64 {
        1.0
    }
}

impl const MulCost<u32> for u32 {
    fn mul_cost() -> f64 {
        1.0
    }
}

impl const MulCost<u64> for u64 {
    fn mul_cost() -> f64 {
        1.0
    }
}

#[bench]
fn mul_u128_bench(bencher: &mut test::Bencher) {
    let a = test::black_box(0x12345678876543219876543223456789_u128);
    let b = test::black_box(0x98765432234567891234567887654321_u128);
    bencher.iter(|| test::black_box(a.wrapping_mul(b)));
}

impl const MulCost<u128> for u128 {
    fn mul_cost() -> f64 {
        7.0
    }
}

use std::ops::{Div, Rem};

#[const_trait]
pub trait DivCost<Rhs = Self>: Div<Rhs> + Rem<Rhs> {
    fn div_cost() -> f64;
}

#[bench]
fn div_u64_bench(bencher: &mut test::Bencher) {
    let a = test::black_box(0x1234567887654321_u64);
    let b = test::black_box(0x9876543223456789_u64);
    bencher.iter(|| test::black_box(a % b));
}

impl const DivCost<u8> for u8 {
    fn div_cost() -> f64 {
        1.0
    }
}

impl const DivCost<u16> for u16 {
    fn div_cost() -> f64 {
        1.0
    }
}

impl const DivCost<u32> for u32 {
    fn div_cost() -> f64 {
        1.0
    }
}

impl const DivCost<u64> for u64 {
    fn div_cost() -> f64 {
        1.0
    }
}

#[bench]
fn div_u128_bench(bencher: &mut test::Bencher) {
    let a = test::black_box(0x12345678876543219876543223456789_u128);
    let b = test::black_box(0x98765432234567891234567887654321_u128);
    bencher.iter(|| test::black_box(a % b));
}

impl const DivCost<u128> for u128 {
    fn div_cost() -> f64 {
        7.0
    }
}
