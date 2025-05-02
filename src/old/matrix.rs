use crate::PolyRing;
use crate::Vector;

#[derive(Clone)]
/// A matrix with a variable number of rows and columns.
pub struct Matrix<T> {
    /// All cells in the matrix, row-first.
    pub cells: Vec<T>,
    /// Number of rows in matrix.
    pub rows: usize,
    /// Number of columns in matrix.
    pub columns: usize,
}

impl<T> Matrix<T> {
    /// Creates a `Matrix` from a flat `Vec`.
    ///
    /// # Example
    /// ```rust
    /// # use crtypes_algebra::Matrix;
    /// let m: Matrix<u8> = Matrix::from_vec(
    ///     4, 4,
    ///     vec![
    ///         0, 1, 2, 3,
    ///			4, 5, 6, 7,
    ///         8, 9, 10, 11,
    ///         12, 13, 14, 15,
    ///		]
    ///	);
    /// ```
    pub fn from_vec(rows: usize, columns: usize, cells: Vec<T>) -> Self {
        debug_assert!(rows * columns == cells.len());
        Matrix {
            cells: cells,
            rows: rows,
            columns: columns,
        }
    }

    /// Creates a `Matrix` from a closure that
    /// initializes each element.
    ///
    /// # Example
    /// ```rust
    /// # use crtypes_algebra::Matrix;
    /// let m: Matrix<u8> = Matrix::from_fn(
    ///     4, 4,
    ///     |y, x| if y == x { 1 } else { 0 }
    ///	);
    /// ```
    pub fn from_fn<F: Fn(usize, usize) -> T>(rows: usize, columns: usize, f: F) -> Self {
        Matrix {
            cells: itertools::iproduct!(0..rows, 0..columns)
                .map(|(y, x)| f(y, x))
                .collect(),
            rows: rows,
            columns: columns,
        }
    }

    /// Computes the transpose of a `Matrix`.
    ///
    /// # Example
    /// ```rust
    /// # use crtypes_algebra::Matrix;
    /// let m: Matrix<u8> = Matrix::from_vec(
    ///     2, 2,
    ///     vec![
    ///         1, 2,
    ///         3, 4,
    ///     ]
    ///	);
    /// let t = m.transpose();
    /// assert_eq!(t.cells, vec![
    /// 	1, 3,
    ///     2, 4,
    /// ]);
    /// ```
    pub fn transpose(&self) -> Self
    where
        T: Clone,
    {
        Self::from_fn(self.columns, self.rows, |y, x| self[(x, y)].clone())
    }

    /// Maps all cells of a `Matrix`.
    ///
    /// # Example
    /// ```rust
    /// # use crtypes_algebra::Matrix;
    /// let m: Matrix<u8> = Matrix::from_vec(
    ///     2, 2,
    ///     vec![
    ///         1, 2,
    ///         3, 4,
    ///     ]
    ///	);
    /// let p = m.map(|x| 2 * x);
    /// assert_eq!(p.cells, vec![
    /// 	2, 4,
    ///     6, 8,
    /// ]);
    /// ```
    pub fn map<U, F: Fn(&T) -> U>(&self, f: F) -> Matrix<U> {
        Matrix {
            cells: self.cells.iter().map(f).collect(),
            rows: self.rows,
            columns: self.columns,
        }
    }

    /// Stretches a `Matrix`, replacing each cell with multiple cells.
    ///
    /// # Example
    /// ```rust
    /// # use crtypes_algebra::Matrix;
    /// let m: Matrix<u8> = Matrix::from_vec(
    ///     2, 2,
    ///     vec![
    ///         1, 2,
    ///         3, 4,
    ///     ]
    ///	);
    /// let p = m.stretch_horizontal(|x| [*x; 2]);
    /// assert_eq!(p.cells, vec![
    /// 	1, 1, 2, 2,
    ///     3, 3, 4, 4,
    /// ]);
    /// ```
    pub fn stretch_horizontal<const N: usize, U, F: Fn(&T) -> [U; N]>(&self, f: F) -> Matrix<U> {
        Matrix {
            cells: self.cells.iter().map(f).flatten().collect(),
            rows: self.rows * N,
            columns: self.columns,
        }
    }
}

impl<T: Clone + std::ops::Mul<Output = T> + std::iter::Sum> Matrix<T> {
    fn mul_naive(&self, rhs: &Self) -> Self {
        debug_assert!(self.columns == rhs.rows);
        Self::from_fn(self.rows, rhs.columns, |y, x| {
            std::iter::zip(
                (0..self.columns).map(|i| self[(y, i)].clone()),
                (0..rhs.rows).map(|i| rhs[(i, x)].clone()),
            )
            .map(|(a, b)| a * b)
            .sum()
        })
    }
}

impl<T: Clone + std::ops::Mul<Output = T> + std::iter::Sum> std::ops::Mul<&Self> for Matrix<T> {
    type Output = Self;

    fn mul(self, rhs: &Self) -> Self {
        self.mul_naive(rhs)
    }
}

impl<T: Clone + std::ops::Mul<Output = T>> std::ops::Mul<T> for Matrix<T> {
    type Output = Self;

    fn mul(self, rhs: T) -> Self {
        self.map(|x: &T| x.clone() * rhs.clone())
    }
}

impl<T: Clone> Matrix<T> {
    /// Given a matrix `self` and a `Vector` of `PolyRing`
    /// where the _i_th element's _j_th coefficient is
    /// given by `a[i][j]`, returns **A** · _self_, with **A**
    /// equal to:
    /// ```text
    ///  _                                               _
    /// |  a[0][0]   a[0][1] ... a[0][N-1]  a[1][0]   ... |
    /// | -a[0][N-1] a[0][0] ... a[0][N-2] -a[1][N-1] ... |
    /// |_   ...       ...   ...    ...        ...    ..._|
    /// ```
    /// Here, _d_ is the size of the `PolyRing` elements,
    /// and the maximum number of columns is `self.rows`, which
    /// must not be larger than `N` · `a.len()`.
    pub fn mul_negacyclic<
        const N: usize,
        U: Clone + From<T> + std::ops::Mul<Output = U> + std::iter::Sum,
    >(
        &self,
        a: Vector<PolyRing<N, U>>,
    ) -> Matrix<U> {
        // TODO: implement alternate algorithm using NTT
        debug_assert!(self.rows <= N * a.len());
        let nega = Matrix::from_fn(N, self.rows, |y, x| {
            let i = x / N;
            let xj = x % N;
            if xj >= y {
                a[i][xj - y].clone()
            } else {
                a[i][N + xj - y].clone()
            }
        });
        Matrix::from_fn(N, self.columns, |y, x| {
            (0..self.rows)
                .map(|i| nega[(y, i)].clone() * U::from(self[(i, x)].clone()))
                .sum()
        })
    }
}

impl<T> std::ops::Index<(usize, usize)> for Matrix<T> {
    type Output = T;

    fn index(&self, index: (usize, usize)) -> &Self::Output {
        &self.cells[index.0 * self.columns + index.1]
    }
}
