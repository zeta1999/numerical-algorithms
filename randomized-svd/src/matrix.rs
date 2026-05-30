//! QR decomposition using Modified Gram-Schmidt with re-orthogonalization.
//!
//! For rank-deficient matrices, a single pass of MGS may leave noise columns
//! that are not truly orthogonal to the signal columns. We apply a second pass
//! (re-orthogonalization) to ensure numerical orthogonality.

use ndarray::Array2;

/// QR decomposition returning only the Q factor's first p columns.
///
/// For an input with `ncols` columns, if `p <= ncols`, returns the first
/// `p` orthonormal columns. If `p > ncols`, pads with identity columns
/// (use with caution).
pub fn qr_q(a: &Array2<f64>, p: usize) -> Array2<f64> {
    let (m, n) = a.dim();
    let mut q = a.clone(); // working copy, m×n

    // --- First pass: Modified Gram-Schmidt ---
    for j in 0..n {
        for i in 0..j {
            let dot: f64 = (0..m).map(|k| q[(k, i)] * q[(k, j)]).sum();
            for k in 0..m {
                q[(k, j)] -= dot * q[(k, i)];
            }
        }
        let norm: f64 = (0..m).map(|k| q[(k, j)].powi(2)).sum::<f64>().sqrt();
        if norm > 1e-300 {
            for k in 0..m {
                q[(k, j)] /= norm;
            }
        }
    }

    // --- Second pass: re-orthogonalize against ALL columns ---
    // This fixes non-orthogonality for rank-deficient matrices where
    // noise columns may not be orthogonal to signal columns after pass 1.
    for j in 0..n {
        for i in 0..n {
            if i == j { continue; }
            let dot: f64 = (0..m).map(|k| q[(k, i)] * q[(k, j)]).sum();
            for k in 0..m {
                q[(k, j)] -= dot * q[(k, i)];
            }
        }
        let norm: f64 = (0..m).map(|k| q[(k, j)].powi(2)).sum::<f64>().sqrt();
        if norm > 1e-300 {
            for k in 0..m {
                q[(k, j)] /= norm;
            }
        }
    }

    // Build m×p Q matrix: first min(m,n) columns from QR, pad with identity if p > min(m,n)
    let out_cols = p;
    let mut result = Array2::<f64>::zeros((m, out_cols));
    for i in 0..m {
        for j in 0..out_cols {
            result[(i, j)] = if j < n { q[(i, j)] } else { if i == j { 1.0 } else { 0.0 } };
        }
    }
    result
}
