use crate::*;
use rand::{distributions::Standard, Rng};

/// Discrete Gaussian distribution with optional parameter.
pub struct DiscreteGaussianDyn<'a, C> {
    pub ctx: &'a C,
    pub sigma: f64,
    m_sigma2_2: f64, // -sigma ^ 2 * 2
    norm: f64,       // normalization coefficient
}

impl<'a, C> DiscreteGaussianDyn<'a, C> {
    fn weight(x: f64, m_sigma2_2: f64) -> f64 {
        f64::exp(x.powi(2) / m_sigma2_2)
    }

    /// Creates a new distribution object with zero mean and a certain standard deviation (`sigma`).
    pub fn new(sigma: f64, ctx: &'a C) -> Self {
        let m_sigma2_2 = -2.0 * sigma.powi(2);
        let mut x = 0.0;
        let mut norm = Self::weight(x, m_sigma2_2);
        loop {
            let new_norm = norm + 2.0 * Self::weight(x, m_sigma2_2);
            let new_x = x + 1.0;
            if new_norm == norm || new_x == x {
                break;
            }
            norm = new_norm;
            x = new_x;
        }
        norm = 1.0 / norm;
        Self {
            ctx,
            sigma,
            m_sigma2_2,
            norm,
        }
    }

    fn prob(&self, x: f64) -> f64 {
        self.norm * Self::weight(x, self.m_sigma2_2)
    }

    /// Default implementation, efficient for small standard deviations.
    pub fn sample_small<
        T: ClosedAddDyn<C> + ClosedSubDyn<C> + ZeroDyn<C> + OneDyn<C>,
        R: ?Sized + Rng,
    >(
        &self,
        rng: &mut R,
    ) -> T {
        loop {
            let mut r = T::zero_d(self.ctx);
            let mut x = 0.0;
            if rng.sample::<f64, _>(Standard) < self.prob(x) {
                return r;
            }
            loop {
                let new_x = x + 1.0;
                if new_x == x {
                    break;
                }
                x = new_x;
                r.add_assign_d(&T::one_d(self.ctx), self.ctx);
                let prob = 2.0 * self.prob(x);
                if prob == 0.0 {
                    break;
                }
                if rng.sample::<f64, _>(Standard) < prob {
                    return if rng.sample(Standard) {
                        T::zero_d(self.ctx).sub_d(&r, self.ctx)
                    } else {
                        r
                    };
                }
            }
        }
    }
}
