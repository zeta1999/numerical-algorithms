//! Randomized SVD algorithm.
//!
//! Implements the subspace iteration method from
//! Halko, Martinsson, Tropp (2011) "Finding Structure with Randomness".
//! Also includes PerSVD: pass-efficient randomized SVD with shifted power
//! iteration (Feng, Yu, Xie, ECML PKDD 2022).

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
    let (u_b, s, vt) = svd_from_eig(&b);

    // Step 6: Map back to original space: U = Q * U_B
    assert_eq!(q.ncols(), u_b.nrows(),
        "Dimension mismatch: q.ncols()={} != u_b.nrows()={}", q.ncols(), u_b.nrows());
    let u = q.dot(&u_b); // m × p

    RandSVDResult { q, u, s, vt }
}

/// SVD of a matrix via eigen-decomposition.
/// Uses A^T A when m > n (economy SVD via right singular vectors),
/// or A A^T when m <= n (via left singular vectors).
fn svd_from_eig(a: &Array2<f64>) -> (Array2<f64>, Vec<f64>, Array2<f64>) {
    let (m, n) = a.dim();

    if m >= n {
        // Use A^T A (n×n) — economy SVD via right singular vectors
        // A = U * S * V^T where U is m×n, S is n×n, V is n×n
        let ata = a.t().dot(a); // n×n
        let (eigenvalues, v) = sym_eig(&ata); // eigenvalues in descending order

        // Singular values
        let s: Vec<f64> = eigenvalues.iter()
            .filter(|&&e| e > 1e-16)
            .map(|&e| e.sqrt())
            .collect();

        // U = A * V * S^{-1}
        let k = s.len();
        let mut u = Array2::<f64>::zeros((m, k));
        for j in 0..k {
            for i in 0..m {
                let val: f64 = (0..n).map(|r| a[(i, r)] * v[(r, j)]).sum::<f64>();
                u[(i, j)] = if s[j] > 1e-16 { val / s[j] } else { 0.0 };
            }
        }

        // V^T as matrix (n × n)
        let vt = v.slice(ndarray::s![.., ..n]).to_owned();

        (u, s, vt)
    } else {
        // Use A A^T (m×m) — left singular vectors via eigen-decomposition
        let ata = a.dot(&a.t()); // m×m
        let (eigenvalues, v) = sym_eig(&ata); // eigenvalues in descending order

        let s: Vec<f64> = eigenvalues.iter()
            .filter(|&&e| e > 1e-16)
            .map(|&e| e.sqrt())
            .collect();

        let p_cols = m;
        let mut u = Array2::<f64>::zeros((m, p_cols));
        for j in 0..p_cols {
            for i in 0..m {
                u[(i, j)] = v[(i, j)];
            }
        }

        // V^T = S^{-1} U^T A
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
}

/// Low-rank approximation: Â = U * diag(S) * V^T.
pub fn low_rank_approx(result: &RandSVDResult, k: usize) -> Array2<f64> {
    let k = k.min(result.s.len()).min(result.u.ncols());
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

// == PerSVD — Pass-efficient randomized SVD with shifted power iteration ==
//
// Reference: Feng, Yu, Xie. "Pass-efficient randomized SVD with boosted
// accuracy." ECML PKDD 2022.
// Code: https://github.com/THU-numbda/PerSVD
//
// Key idea: Use shifted power iteration to amplify dominant singular vectors,
// reducing the effective condition number and achieving 3-4 orders of magnitude
// better accuracy with fewer data passes (3-4 vs 5+ for standard R-SVD).

/// Parameters for PerSVD algorithm.
pub struct PerSVDParams {
    /// Oversampling parameter.
    pub ost: usize,
    /// Number of power iteration rounds.
    pub power_iters: usize,
    /// Shift update strategy.
    pub shift_type: PerSVDShift,
}

/// Type of shift parameter update for PerSVD.
#[derive(Clone, Copy)]
pub enum PerSVDShift {
    Once,
    Adaptive,
}

impl Default for PerSVDParams {
    fn default() -> Self {
        PerSVDParams { ost: 10, power_iters: 0, shift_type: PerSVDShift::Adaptive }
    }
}

/// PerSVD: Pass-efficient randomized SVD with shifted power iteration.
///
/// Reference: Feng, Yu, Xie. "Pass-efficient randomized SVD with boosted
/// accuracy." ECML PKDD 2022.
/// Code: https://github.com/THU-numbda/PerSVD
///
/// Current implementation: wraps the standard randomized SVD.
/// The full PerSVD algorithm with shifted power iteration and dynamic
/// shift parameter requires careful numerical implementation.
/// TODO: Implement the complete PerSVD algorithm with:
/// - Shifted power iteration: Q = svd(A^T*A*Q - alpha*Q)
/// - Adaptive shift: alpha = (alpha + sigma_min) / 2
/// - Proper economy SVD decomposition
pub fn per_svd(a: &Array2<f64>, params: PerSVDParams) -> RandSVDResult {
    // Use standard randomized SVD as baseline
    // Full PerSVD with shifted power iteration to be implemented
    randomized_svd(a, params.ost.min(a.nrows().min(a.ncols()) - params.ost),
        params.ost, params.power_iters)
}

/// (Reserved for future PerSVD implementation)
/// Economy SVD via eigendecomposition of A^T A.
/// Returns (U, S, V) where U is m×min(m,k) (left SVs), S is Vec (singular values),
/// and V is min(m,k)×min(m,k) (right SVs as columns).
#[allow(dead_code)]
fn svd_economy(a: &Array2<f64>) -> (Array2<f64>, Vec<f64>, Array2<f64>) {
    let (m, k_in) = a.dim();
    let p = m.min(k_in);

    let ata = a.t().dot(a);
    let (eigenvalues, v) = sym_eig(&ata);

    let s: Vec<f64> = eigenvalues.iter()
        .take(p)
        .map(|&e| e.max(0.0).sqrt())
        .collect();

    let k = s.len();
    let mut u = Array2::<f64>::zeros((m, k));
    for j in 0..k {
        for i in 0..m {
            let val: f64 = (0..k_in).map(|r| a[(i, r)] * v[(r, j)]).sum::<f64>();
            u[(i, j)] = if s[j] > 1e-16 { val / s[j] } else { 0.0 };
        }
    }

    let vt = v.slice(ndarray::s![.., ..p]).to_owned();
    (u, s, vt)
}
