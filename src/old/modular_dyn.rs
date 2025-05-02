use crate::*;
use noether::*;
use num_traits::*;
use std::ops::*;

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ModularDyn<T: Sized> {
    /// The underlying raw integer.
    pub inner: T,
    /// The modulo, stored at runtime.
    pub modulo: T,
}

//   ____                              _
//  / ___|___  _ ____   _____ _ __ ___(_) ___  _ __
// | |   / _ \| '_ \ \ / / _ \ '__/ __| |/ _ \| '_ \
// | |__| (_) | | | \ V /  __/ |  \__ \ | (_) | | | |
//  \____\___/|_| |_|\_/ \___|_|  |___/_|\___/|_| |_|
//

impl<T: PartialOrd> ModularDyn<T> {
	pub fn new(inner: T, modulo: T) -> Self {
		debug_assert!(inner < modulo);
		Self {
			inner: inner,
			modulo: modulo,
		}
	}
}

//     _       _     _ _ _   _
//    / \   __| | __| (_) |_(_)_   _____
//   / _ \ / _` |/ _` | | __| \ \ / / _ \
//  / ___ \ (_| | (_| | | |_| |\ V /  __/
// /_/   \_\__,_|\__,_|_|\__|_| \_/ \___|
//

impl<T: Clone + PartialOrd + Zero + WrappingAdd + WrappingSub + One> Add
    for ModularDyn<T>
{
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
    	debug_assert!(self.modulo == rhs.modulo);
        let sum = self.inner.wrapping_add(&rhs.inner);
        let power_of_two = self.modulo.clone() - T::one() == T::zero().wrapping_sub(&T::one()).into();
        let r = if power_of_two {
            sum
        } else {
            let wraparound = self.modulo.clone().wrapping_add(&(self.modulo.clone() - T::one())) > T::zero().wrapping_sub(&T::one()).into();
            if wraparound && sum < rhs.inner
                || !wraparound && sum > self.modulo.clone()
            {
                sum - self.modulo.clone()
            } else {
                sum
            }
        };
        Self { inner: r, modulo: self.modulo }
    }
}

//  __  __       _ _   _       _ _           _   _
// |  \/  |_   _| | |_(_)_ __ | (_) ___ __ _| |_(_)_   _____
// | |\/| | | | | | __| | '_ \| | |/ __/ _` | __| \ \ / / _ \
// | |  | | |_| | | |_| | |_) | | | (_| (_| | |_| |\ V /  __/
// |_|  |_|\__,_|_|\__|_| .__/|_|_|\___\__,_|\__|_| \_/ \___|
//

/*impl<T: Clone + Bounded + PartialEq + PartialOrd + Zero + ClosedAdd + ClosedSub + One + WideningMul> Mul for ModularDyn<T>
{
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
    	debug_assert!(self.modulo == rhs.modulo);
        let (low, high) = self.inner.wdmul(&rhs.inner);
        let coeff = Self::new(T::max_value(), self.modulo.clone()) + Self::new(T::one(), self.modulo.clone());
        if high.is_zero() {
            Self::new(low % self.modulo.clone(), self.modulo)
        } else {
            let prod = Self::new(high, self.modulo.clone()) * coeff;
            Self::new(low % self.modulo.clone(), self.modulo) + prod
        }
    }
}*/
