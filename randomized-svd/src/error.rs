//! Error metrics for evaluating SVD approximation quality.

use ndarray::Array2;

/// Frobenius norm of a matrix: sqrt(sum of squared entries).
pub fn frobenius_norm(a: &Array2<f64>) -> f64 {
    a.iter().map(|&x| x * x).sum::<f64>().sqrt()
}

/// Relative Frobenius norm error: ||A - B||_F / ||A||_F.
///
/// Returns 0.0 if ||A||_F is zero.
pub fn relative_frobenius_error(a: &Array2<f64>, b: &Array2<f64>) -> f64 {
    let norm_a = frobenius_norm(a);
    if norm_a < 1e-300 {
        return 0.0;
    }
    let diff: f64 = a.iter().zip(b.iter()).map(|(&x, &y)| (x - y).powi(2)).sum();
    diff.sqrt() / norm_a
}

/// Spectral norm (infinity-norm approximation): max_i sum_j |a[i, j]|.
///
/// This is a cheap upper bound on the true spectral (L2) norm.
pub fn spectral_norm_inf(a: &Array2<f64>) -> f64 {
    let mut max_row = 0.0f64;
    for row in a.outer_iter() {
        let row_sum: f64 = row.iter().map(|&x| x.abs()).sum();
        if row_sum > max_row {
            max_row = row_sum;
        }
    }
    max_row
}

/// Relative spectral norm error: ||A - B||_inf / ||A||_inf.
pub fn relative_spectral_error(a: &Array2<f64>, b: &Array2<f64>) -> f64 {
    let norm_a = spectral_norm_inf(a);
    if norm_a < 1e-300 {
        return 0.0;
    }
    let mut max_diff = 0.0f64;
    for i in 0..a.nrows() {
        let row_sum: f64 = (0..a.ncols()).map(|j| (a[(i, j)] - b[(i, j)]).abs()).sum();
        if row_sum > max_diff {
            max_diff = row_sum;
        }
    }
    max_diff / norm_a
}
