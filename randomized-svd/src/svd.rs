//! Randomized SVD algorithm.
//!
//! Implements the subspace iteration method from
//! Halko, Martinsson, Tropp (2011) "Finding Structure with Randomness".

use ndarray::Array2;
use rand::SeedableRng;
use rand_distr::{Distribution, Normal};

use crate::error::{relative_frobenius_error, relative_spectral_error};
use crate::eigen::sym_eig;
use crate::matrix::qr_q;

/// Randomized SVD result.
pub struct RandSVDResult {
    pub q: Array2<f64>,
    pub u: Array2<f64>,
    pub s: Vec<f64>,
    pub vt: Array2<f64>,
}

/// Approximate rank-k SVD using randomized subspace iteration.
///
/// # Arguments
/// * `a` — Input matrix (m × n)
/// * `k` — Target rank
/// * `ost` — Oversampling parameter (default 10). Uses p = k + ost random probes.
/// * `power_iters` — Number of power iteration rounds (default 0).
///
/// # Algorithm (Halko–Martinsson–Tropp 2011)
///
/// 1. Generate random Gaussian probe matrix Ω ∈ ℝ^{n×p}, p = k + ost
/// 2. Subspace iteration: Y = A Ω (optionally with power iterations)
/// 3. QR factorization: Y ≈ Q R, where Q ∈ ℝ^{m×p} has orthonormal columns
/// 4. Project A onto Q: B = Q^T A ∈ ℝ^{p×n}
/// 5. Compute SVD of small matrix: B = U_B Σ V^T
/// 6. Return U = Q U_B, S = Σ, V^T
///
/// # Reference
///
/// Halko, N., Martinsson, P.-G., & Tropp, J. A. (2011). Finding Structure
/// with Randomness: Probabilistic Algorithms for Constructing Approximate
/// Matrix Decompositions. SIAM Review, 53(2), 217–288.
pub fn randomized_svd(a: &Array2<f64>, k: usize, ost: usize, power_iters: usize) -> RandSVDResult {
    let (m, n) = a.dim();
    let p = k + ost.min(m.min(n) - k); // ensure p doesn't exceed available rank

    // Step 1: Random Gaussian probe matrix (n × p)
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let normal = Normal::new(0.0, 1.0).unwrap();
    let omega_data: Vec<f64> = normal.sample_iter(&mut rng).take(n * p).collect();
    let omega = Array2::from_shape_vec((n, p), omega_data).unwrap();

    // Step 2: Randomized subspace iteration
    let mut y = a.dot(&omega); // m × p
    for _ in 0..power_iters {
        let at_y = &a.t().dot(&y); // n × p
        y = a.dot(at_y); // m × p
    }

    // Step 3: QR → orthonormal basis Q (m × p)
    let q = qr_q(&y, p); // m × p

    // Step 4: Project A onto Q: B = Q^T A (p × n)
    let b = q.t().dot(a); // p × n

    // Step 5: SVD of small matrix B = U_B Σ V^T
    // U_B is p × k (eigenvectors of B B^T)
    // V^T is k × n (right singular vectors)
    let (u_b, s, vt) = svd_from_eig(&b);

    // Step 6: Map back to original space: U = Q * U_B (m × p × (p × k) → m × k)
    // Verify dimensions: q.ncols() must equal u_b.nrows()
    assert_eq!(q.ncols(), u_b.nrows(),
        "Dimension mismatch: q.ncols()={} != u_b.nrows()={}", q.ncols(), u_b.nrows());
    let u = q.dot(&u_b); // m × k

    RandSVDResult { q, u, s, vt }
}

/// SVD of a matrix via eigen-decomposition of A A^T.
///
/// Returns (U, S, V^T) where A = U diag(S) V^T.
///
/// For production use, consider Golub-Kahan bidiagonalization (as in
/// LAPACK's `dgejsvd`) for better numerical stability.
fn svd_from_eig(a: &Array2<f64>) -> (Array2<f64>, Vec<f64>, Array2<f64>) {
    let (m, n) = a.dim();

    // Compute A A^T (m×m symmetric)
    let ata = a.dot(&a.t()); // m×m

    // Eigenvalue decomposition: A A^T = V Λ V^T
    // V columns are eigenvectors, eigenvalues are in descending order
    let (eigenvalues, v) = sym_eig(&ata);

    // Extract singular values: σ_i = sqrt(λ_i) for λ_i > 0
    let p = m.min(n);
    let s: Vec<f64> = eigenvalues
        .iter()
        .filter(|&&e| e > 1e-16)
        .map(|&e| e.sqrt())
        .take(p)
        .collect();

    // The input matrix a has shape (m, n) where m = p (from randomized SVD context).
    // We always return exactly p columns in u (matching the input's row count).
    let p_cols = m; // rows of a = columns of q that we'll multiply with
    let mut u = Array2::<f64>::zeros((m, p_cols));
    for j in 0..p_cols {
        for i in 0..m {
            u[(i, j)] = v[(i, j)]; // v's j-th column is eigenvector
        }
    }

    // V^T = S^{-1} U^T A (for columns with positive singular values, zero-padded for rest)
    let k = s.len();
    let mut vt = Array2::<f64>::zeros((p_cols, n));
    for j in 0..k {
        for i in 0..n {
            let val: f64 = (0..m).map(|l| u[(l, j)] * a[(l, i)]).sum::<f64>() / s[j];
            vt[(j, i)] = val;
        }
    }

    (u, s, vt)
}

/// Low-rank approximation: Â = U * diag(S) * V^T.
pub fn low_rank_approx(result: &RandSVDResult, k: usize) -> Array2<f64> {
    let u_k = result.u.slice(ndarray::s![.., ..k]).to_owned();
    let s_k: Vec<f64> = result.s[..k].to_vec();
    let vt_k = result.vt.slice(ndarray::s![..k, ..]).to_owned();

    let (m, r) = u_k.dim();
    let _vr = vt_k.nrows();
    let n = vt_k.ncols();

    // A_hat[i,j] = sum_l U[i,l] * S[l] * Vt[l,j]
    let mut approx = Array2::<f64>::zeros((m, n));
    for i in 0..m {
        for j in 0..n {
            let val: f64 = (0..r).map(|l| u_k[(i, l)] * s_k[l] * vt_k[(l, j)]).sum();
            approx[(i, j)] = val;
        }
    }

    approx
}

/// Compute approximation errors.
pub fn svd_errors(a: &Array2<f64>, result: &RandSVDResult, k: usize) -> (f64, f64) {
    let approx = low_rank_approx(result, k);
    let frob = relative_frobenius_error(a, &approx);
    let spec = relative_spectral_error(a, &approx);
    (frob, spec)
}
