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

/// SVD of a matrix via eigen-decomposition of A^T A.
///
/// Returns (U, S, V^T) for economy SVD where:
/// - U is m×k (left singular vectors), k = min(rank, p)
/// - S is a Vec of k singular values in descending order
/// - V^T is k×n (right singular vectors transposed)
///
/// Invariant: u.ncols() == s.len() == vt.nrows(), and vt.ncols() == a.ncols().
fn svd_from_eig(a: &Array2<f64>) -> (Array2<f64>, Vec<f64>, Array2<f64>) {
    let (m, n) = a.dim();
    let p = m.min(n); // max possible rank

    // A^T A is n×n; its eigenvectors are the right singular vectors of A.
    let ata = a.t().dot(a); // n×n
    let (eigenvalues, v) = sym_eig(&ata);

    // Filter and take at most p eigenvalues
    let filtered: Vec<f64> = eigenvalues.iter()
        .filter(|&&e| e > 1e-16)
        .copied()
        .take(p)
        .collect();

    // Singular values = sqrt(eigenvalues)
    let s: Vec<f64> = filtered.iter()
        .map(|&e| e.sqrt())
        .collect();
    let k = s.len();

    // Left singular vectors: U = A * V_k * S_k^{-1}
    // V_k columns = first k eigenvectors = right singular vectors
    let mut u = Array2::<f64>::zeros((m, k));
    for j in 0..k {
        for i in 0..m {
            let val: f64 = (0..n).map(|r| a[(i, r)] * v[(r, j)]).sum::<f64>();
            u[(i, j)] = if s[j] > 1e-16 { val / s[j] } else { 0.0 };
        }
    }

    // V^T: k×n matrix whose rows are the first k right singular vectors.
    // v is n×n; slice first k columns (n×k), then transpose → k×n.
    let vt = v.slice(ndarray::s![.., ..k]).to_owned(); // n×k
    let vt = vt.reversed_axes(); // k×n
    (u, s, vt)
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
#[derive(Clone)]
pub struct PerSVDParams {
    /// Oversampling parameter.
    pub ost: usize,
    /// Number of power iteration rounds.
    pub power_iters: usize,
    /// Shift update strategy.
    pub shift_type: PerSVDShift,
}

/// Type of shift parameter update for PerSVD.
#[derive(Clone, Copy, PartialEq)]
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
/// The key contribution of PerSVD is the **shifted power iteration** which
/// amplifies dominant singular vectors by applying (A^T A - alpha I) instead
/// of just A^T A. This reduces the effective condition number and achieves
/// better accuracy with fewer data passes.
///
/// Implementation:
/// 1. Right-space basis Q via QR(Omega)
/// 2. Shifted power iterations to amplify dominant subspace
/// 3. Standard randomized SVD final step:
///    a. Y = A * Q, Q_y = QR(Y)  — orthonormal left SV estimate
///    b. B = Q_y^T * A             — small l×n projected matrix
///    c. SVD(B) = U_b * S_b * V_b^T
///    d. U = Q_y * U_b
pub fn per_svd(a: &Array2<f64>, params: PerSVDParams) -> RandSVDResult {
    let (m, n) = a.dim();
    let l = (params.ost + params.power_iters).min(m.min(n));

    if l == 0 {
        return per_svd(a, PerSVDParams { ost: 1, ..params });
    }

    // Step 1: Random probe Omega (n × l)
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let normal = Normal::new(0.0, 1.0).unwrap();
    let omega: Array2<f64> = Array2::from_shape_vec((n, l),
        normal.sample_iter(&mut rng).take(n * l).collect()).unwrap();

    // Step 2: Initial Q = qr(Omega, 0) — thin QR of n×l → Q is n×l
    let mut q = qr_q(&omega, l); // n × l

    let mut alpha: f64 = 0.0;

    // Step 3: Shifted power iterations
    for _ in 0..params.power_iters {
        // Y = A * Q (m × l)
        let y = a.dot(&q);

        // W = A^T * Y (n × l) = A^T * A * Q
        let wt = a.t().dot(&y);

        // Shifted matrix: M = W - alpha * Q (n × l)
        let shifted: Array2<f64> = (&wt - &q * alpha).to_owned();

        // Q = qr(M, 0) — orthonormal basis of M, preserves n × l shape
        q = qr_q(&shifted, l); // n × l

        // Update alpha — adaptive shift
        if params.shift_type == PerSVDShift::Adaptive {
            let m_norm: f64 = shifted.iter().map(|&x| x * x).sum::<f64>().sqrt();
            if m_norm > 1e-16 && alpha < m_norm {
                alpha = (alpha + m_norm) / 2.0;
            }
        }
    }

    // Step 4: Compute Y = A * Q (m × l) — left SV estimate
    let y = a.dot(&q); // m × l

    // QR of Y: Y = Q_y * R → Q_y is m×l orthonormal basis
    let qy = qr_q(&y, l); // m × l

    // Step 5: Project A onto Q_y: B = Q_y^T * A (l × n)
    let b = qy.t().dot(a); // l × n

    // Step 6: SVD of small matrix B (l × n): B = U_b * S_b * V_b^T
    let (u_b, s_b, v_b_t) = svd_from_eig(&b); // U_B: l×k, S: k, V_B^T: k×n
    let k = s_b.len();

    // U = Q_y * U_B (m × l * l × k = m × k)
    // Re-orthogonalize via QR to ensure clean orthonormal U (u_b may have
    // non-orthogonal columns from near-zero SVs).
    let u_temp = qy.dot(&u_b); // m × k
    let u_final = qr_q(&u_temp, k); // re-orthogonalize

    RandSVDResult {
        q: Array2::<f64>::zeros((m, l)),
        u: u_final,
        s: s_b,
        vt: v_b_t,
    }
}

/// Economy SVD via eigendecomposition of A^T A.
///
/// For an m × k_in matrix, returns (U, S, V^T) where:
/// - U is m × k (left singular vectors), k = number of non-zero SVs
/// - S is Vec of k singular values (descending)
/// - V^T is k × k_in (right singular vectors transposed)
///
/// Returns the same shape invariant as `svd_from_eig`:
/// u.ncols() == s.len() == vt.nrows().
#[allow(dead_code)]
fn svd_economy(a: &Array2<f64>) -> (Array2<f64>, Vec<f64>, Array2<f64>) {
    let (m, k_in) = a.dim();
    let p = m.min(k_in);

    // A^T A is k_in × k_in; its eigenvectors = right singular vectors
    let ata = a.t().dot(a); // k_in × k_in
    let (eigenvalues, v) = sym_eig(&ata);

    // Singular values = sqrt(eigenvalues)
    let s: Vec<f64> = eigenvalues.iter()
        .take(p)
        .filter(|&&e| e > 1e-16)
        .map(|&e| e.sqrt())
        .collect();
    let k = s.len();

    // U = A * V_k * S_k^{-1}
    let mut u = Array2::<f64>::zeros((m, k));
    for j in 0..k {
        for i in 0..m {
            let val: f64 = (0..k_in).map(|r| a[(i, r)] * v[(r, j)]).sum::<f64>();
            u[(i, j)] = if s[j] > 1e-16 { val / s[j] } else { 0.0 };
        }
    }

    // V^T: k × k_in (rows = first k right singular vectors)
    let vt = v.slice(ndarray::s![.., ..k]).to_owned(); // k_in × k
    let vt = vt.reversed_axes(); // k × k_in
    (u, s, vt)
}
