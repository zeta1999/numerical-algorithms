//! Symmetric eigenvalue decomposition via the Jacobi method.
//!
//! Computes eigenvalues and eigenvectors of a real symmetric matrix.
//! Used internally by the SVD implementation to extract singular values
//! from A^T A (or A A^T).

use ndarray::Array2;

/// Eigenvalue decomposition of a symmetric matrix.
///
/// Returns (λ, V) where:
/// - λ is a vec of eigenvalues in descending order
/// - V is an n×n matrix where column i is the eigenvector for λ[i]
pub fn sym_eig(a: &Array2<f64>) -> (Vec<f64>, Array2<f64>) {
    let (n, _) = a.dim();
    assert_eq!(n, a.row(0).len(), "Matrix must be square");

    // Copy matrix and initialize eigenvectors to identity
    let mut t = a.clone();
    let mut v = Array2::<f64>::eye(n);

    // Jacobi iterations
    jacobi(&mut t, &mut v, n);

    // Extract eigenvalues and sort descending
    let eigenvalues: Vec<f64> = (0..n).map(|i| t[(i, i)]).collect();
    let mut indexed: Vec<(f64, usize)> = eigenvalues.iter().enumerate().map(|(i, &e)| (e, i)).collect();
    indexed.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap().then(std::cmp::Ordering::Equal));

    let mut sorted_v = Array2::<f64>::zeros((n, n));
    for (rank, &(_, orig_idx)) in indexed.iter().enumerate() {
        for i in 0..n {
            sorted_v[(i, rank)] = v[(i, orig_idx)];
        }
    }

    let sorted_eigenvalues: Vec<f64> = indexed.iter().map(|&(e, _)| e).collect();
    (sorted_eigenvalues, sorted_v)
}

/// Jacobi eigenvalue algorithm for symmetric matrices.
///
/// Repeatedly applies Givens rotations to zero out the largest off-diagonal
/// element until the matrix is diagonal (eigenvalues on the diagonal).
fn jacobi(t: &mut Array2<f64>, v: &mut Array2<f64>, n: usize) {
    let max_iter = n * n * 100;
    let tol = 1e-15;

    for _ in 0..max_iter {
        // Find the largest off-diagonal element
        let mut max_val = 0.0_f64;
        let mut p = 0usize;
        let mut q = 1usize;
        for i in 0..n {
            for j in (i + 1)..n {
                let val = t[(i, j)].abs();
                if val > max_val {
                    max_val = val;
                    p = i;
                    q = j;
                }
            }
        }

        // Converged
        if max_val < tol {
            return;
        }

        // Compute Givens rotation to zero out t[p,q]
        let a_pp = t[(p, p)];
        let a_qq = t[(q, q)];
        let a_pq = t[(p, q)];

        let theta = 0.5_f64 * (2.0 * a_pq).atan2(a_qq - a_pp);
        let c = theta.cos();
        let s = theta.sin();

        // Update diagonal elements
        t[(p, p)] = c * c * a_pp + s * s * a_qq - 2.0 * c * s * a_pq;
        t[(q, q)] = s * s * a_pp + c * c * a_qq + 2.0 * c * s * a_pq;

        // Update off-diagonal elements
        for k in 0..n {
            if k != p && k != q {
                let a_pk = t[(p, k)];
                let a_qk = t[(q, k)];

                // t[k, p] = c*a[k,p] - s*a[k,q]
                // t[k, q] = s*a[k,p] + c*a[k,q]
                t[(k, p)] = c * a_pk - s * a_qk;
                t[(k, q)] = s * a_pk + c * a_qk;

                // Symmetric
                t[(p, k)] = t[(k, p)];
                t[(q, k)] = t[(k, q)];
            }
        }

        // Zero out the target element
        t[(p, q)] = 0.0;
        t[(q, p)] = 0.0;

        // Accumulate rotations in V
        for i in 0..n {
            let v_ip = v[(i, p)];
            let v_iq = v[(i, q)];
            v[(i, p)] = c * v_ip - s * v_iq;
            v[(i, q)] = s * v_ip + c * v_iq;
        }
    }
}
