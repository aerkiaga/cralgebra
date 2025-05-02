/// A vector with a variable number of components.
pub struct Vector<T> {
    pub components: Vec<T>,
}

impl<T> Vector<T> {
    /// Returns the number of components in the `Vector`.
    pub fn len(&self) -> usize {
        self.components.len()
    }
}

impl<T> From<Vec<T>> for Vector<T> {
    fn from(value: Vec<T>) -> Self {
        Vector { components: value }
    }
}

impl<T> std::ops::Index<usize> for Vector<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        &self.components[index]
    }
}

impl<T: std::ops::Add<Output = T>> std::ops::Add for Vector<T> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        std::iter::zip(self.components.into_iter(), rhs.components.into_iter())
            .map(|(x, y)| x + y)
            .collect::<Vec<_>>()
            .into()
    }
}

impl<T: std::ops::Mul<Rhs, Output = T>, Rhs: Clone> std::ops::Mul<Rhs> for Vector<T> {
    type Output = Self;

    fn mul(self, rhs: Rhs) -> Self::Output {
        self.components
            .into_iter()
            .map(|x| x * rhs.clone())
            .collect::<Vec<_>>()
            .into()
    }
}
