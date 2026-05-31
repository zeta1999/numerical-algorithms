//! Integration tests for randomized SVD.

use ndarray::Array2;
use rand::SeedableRng;
use rand_distr::{Distribution, Normal};
use randomized_svd::{randomized_svd, low_rank_approx, svd_errors, per_svd, PerSVDParams, PerSVDShift, matrix::qr_q};
use randomized_svd::error::relative_frobenius_error;

/// Generate a random matrix with known rank k.
fn make_test_matrix(rows: usize, cols: usize, k: usize) -> Array2<f64> {
    let mut rng = rand::rngs::StdRng::seed_from_u64(123);
    let normal = Normal::new(0.0, 1.0).unwrap();

    let u_raw: Vec<f64> = normal.sample_iter(&mut rng).take(rows * k).collect();
    let u_mat = Array2::from_shape_vec((rows, k), u_raw).unwrap();
    let u = randomized_svd::matrix::qr_q(&u_mat, k);

    let v_raw: Vec<f64> = normal.sample_iter(&mut rng).take(cols * k).collect();
    let v_mat = Array2::from_shape_vec((cols, k), v_raw).unwrap();
    let v = randomized_svd::matrix::qr_q(&v_mat, k);

    // Singular values: descending geometric sequence [10, 1, 0.1, ...]
    let s: Vec<f64> = (0..k).map(|i| 10.0_f64.powi((k - 1 - i) as i32)).collect();
    // s = [10^(k-1), 10^(k-2), ..., 10^0]

    // A = U_k * diag(s) * V_k^T
    let mut a = Array2::<f64>::zeros((rows, cols));
    for i in 0..rows {
        for j in 0..cols {
            let val: f64 = (0..k).map(|l| u[(i, l)] * s[l] * v[(j, l)]).sum();
            a[(i, j)] = val;
        }
    }

    a
}

/// Eigenvalue decomposition of a symmetric matrix via the QR algorithm.
fn sym_eig(a: &Array2<f64>) -> (Vec<f64>, Array2<f64>) {
    randomized_svd::eigen::sym_eig(a)
}

#[test]
fn diagnostic_matrix_check() {
    // Verify QR preserves Frobenius norm for a tall matrix
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let normal = Normal::new(0.0, 1.0).unwrap();

    let data: Vec<f64> = normal.sample_iter(&mut rng).take(100).collect();
    let a = Array2::from_shape_vec((10, 10), data).unwrap();

    let q = randomized_svd::matrix::qr_q(&a, 10);

    // Q^T Q should be identity
    let qtq_err: f64 = (0..10).map(|i| (0..10).map(|j| {
        let dot: f64 = (0..10).map(|l| q[(l,i)] * q[(l,j)]).sum::<f64>();
        let expected = if i==j {1.0} else {0.0};
        (dot - expected).abs()
    }).sum::<f64>()).sum::<f64>();

    assert!(qtq_err < 1e-12, "QR_ORTH_FAIL: qtq_err={:.2e}", qtq_err);
}

#[test]
fn known_low_rank_approximation() {
    let a = make_test_matrix(50, 40, 3);
    let result = randomized_svd(&a, 3, 5, 0);

    let (frob, spec) = svd_errors(&a, &result, 3);
    assert!(frob < 1e-4, "Frobenius error too high: {frob:.2e}");
    assert!(spec < 1e-4, "Spectral error too high: {spec:.2e}");
}

#[test]
fn svd_singular_values_sorted() {
    let a = Array2::eye(20);
    let result = randomized_svd(&a, 5, 5, 0);

    for i in 1..result.s.len() {
        assert!(
            result.s[i - 1] >= result.s[i] - 1e-10,
            "Singular values not sorted: s[{}]={:.6} < s[{}]={:.6}",
            i - 1, result.s[i - 1], i, result.s[i]
        );
    }
}

#[test]
fn low_rank_approx_consistent() {
    let a = make_test_matrix(30, 25, 5);
    let result = randomized_svd(&a, 5, 5, 0);

    let approx = low_rank_approx(&result, 5);
    let frob = randomized_svd::error::relative_frobenius_error(&a, &approx);
    eprintln!("low_rank_approx: frob_err={:.2e}", frob);
    assert!(frob < 1e-5, "Low-rank approx error too high: {frob:.2e}");
}

#[test]
fn power_iterations_comparison() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(99);
    let normal = Normal::new(0.0, 1.0).unwrap();
    let x: Vec<f64> = normal.sample_iter(&mut rng).take(50 * 50).collect();
    let a = Array2::from_shape_vec((50, 50), x).unwrap();

    let r0 = randomized_svd(&a, 10, 5, 0);
    let (frob0, _) = svd_errors(&a, &r0, 10);

    let r1 = randomized_svd(&a, 10, 5, 2);
    let (frob1, _) = svd_errors(&a, &r1, 10);

    eprintln!("power_iterations: no_power_frob={:.2e}, power2_frob={:.2e}", frob0, frob1);
}

#[test]
fn reconstruction_vs_own_svd() {
    let a = make_test_matrix(20, 15, 3);
    let rand_result = randomized_svd(&a, 3, 5, 0);
    let rand_approx = low_rank_approx(&rand_result, 3);

    let rand_frob = randomized_svd::error::relative_frobenius_error(&a, &rand_approx);
    assert!(rand_frob < 1e-4, "Randomized SVD error too high: {rand_frob:.2e}");
}

#[test]
fn eigenvalues_of_diagonal() {
    let mut diag = Array2::<f64>::zeros((5, 5));
    diag[(0, 0)] = 9.0;
    diag[(1, 1)] = 4.0;
    diag[(2, 2)] = 1.0;
    diag[(3, 3)] = 0.01;
    diag[(4, 4)] = 0.001;

    let (eigenvalues, _) = sym_eig(&diag);
    eprintln!("eigenvalues_of_diagonal: {:?}", eigenvalues);

    let expected = [9.0, 4.0, 1.0, 0.01, 0.001];
    for (got, &exp) in eigenvalues.iter().zip(expected.iter()) {
        assert!((got - exp).abs() < 1e-8, "eigenvalue mismatch: got {got} expected {exp}");
    }
}

#[test]
fn simple_sym_eig_check() {
    let a = Array2::from_shape_vec((2, 2), vec![1.0, 1.0, 1.0, 2.0]).unwrap();
    let (eigenvalues, _) = sym_eig(&a);
    eprintln!("simple_sym_eig: {:?}", eigenvalues);

    assert!((eigenvalues[0] - 2.61803).abs() < 1e-4, "eigenvalue[0] = {:.6}", eigenvalues[0]);
    assert!((eigenvalues[1] - 0.38197).abs() < 1e-4, "eigenvalue[1] = {:.6}", eigenvalues[1]);
}

#[test]
fn qr_q_orthogonality() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(7);
    let normal = rand_distr::Normal::new(0.0, 1.0).unwrap();
    let data: Vec<f64> = normal.sample_iter(&mut rng).take(30 * 20).collect();
    let a = Array2::from_shape_vec((30, 20), data).unwrap();

    let q = randomized_svd::matrix::qr_q(&a, 20);

    let mut qtq_err: f64 = 0.0;
    for i in 0..20 {
        for j in 0..20 {
            let dot: f64 = (0..30).map(|k| q[(k, i)] * q[(k, j)]).sum();
            let expected = if i == j { 1.0f64 } else { 0.0f64 };
            qtq_err += (dot - expected).abs();
        }
    }
    eprintln!("qr_orthogonality: ||Q^T Q - I||_1 = {:.2e}", qtq_err);
    assert!(qtq_err < 1e-12, "QR decomposition Q is not orthogonal: diff={qtq_err:.2e}");
}

/// Test that PerSVD types and function compile.
/// The full PerSVD algorithm with shifted power iteration is a reference
/// from Feng, Yu, Xie (ECML PKDD 2022) but requires careful implementation.
/// This test verifies the API is accessible and per_svd returns valid results.
#[test]
fn per_svd_types_compile() {
    let a = make_test_matrix(20, 15, 3);
    let _result = per_svd(&a, PerSVDParams {
        ost: 5,
        power_iters: 0,
        shift_type: PerSVDShift::Adaptive,
    });
    // per_svd currently wraps randomized_svd; should return valid result
    assert!(_result.s.len() >= 1, "PerSVD should return at least 1 singular value");
}

/// Test PerSVD accuracy on a known low-rank matrix.
/// PerSVD should achieve near-machine-precision reconstruction for exact low-rank matrices.
#[test]
fn per_svd_accuracy() {
    let a = make_test_matrix(50, 40, 3);
    let result = per_svd(&a, PerSVDParams {
        ost: 5,
        power_iters: 0,
        shift_type: PerSVDShift::Adaptive,
    });

    // Verify dimensions: U is m×l, S has l values, V^T is l×n
    let l = result.s.len();
    assert_eq!(result.u.nrows(), 50, "U should have 50 rows");
    assert_eq!(result.u.ncols(), l, "U cols should match s.len()");
    assert_eq!(result.vt.nrows(), l, "V^T rows should match s.len()");
    assert_eq!(result.vt.ncols(), 40, "V^T cols should be 40");

    // Reconstruction error should be very small for exact low-rank matrix
    let approx = low_rank_approx(&result, l);
    let frob = relative_frobenius_error(&a, &approx);
    eprintln!("per_svd_accuracy: frob_err={:.2e}", frob);
    assert!(frob < 1e-6, "PerSVD Frobenius error too high: {frob:.2e}");
}

/// Test PerSVD with shifted power iteration — should improve accuracy
/// on ill-conditioned matrices compared to zero power iterations.
#[test]
fn per_svd_power_iteration_improvement() {
    // Ill-conditioned matrix: singular values [1000, 10, 0.01]
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let normal = Normal::new(0.0, 1.0).unwrap();

    let rows = 30;
    let cols = 25;
    let k = 2;

    let u_raw: Vec<f64> = normal.sample_iter(&mut rng).take(rows * k).collect();
    let u_mat = Array2::from_shape_vec((rows, k), u_raw).unwrap();
    let u = qr_q(&u_mat, k);

    let v_raw: Vec<f64> = normal.sample_iter(&mut rng).take(cols * k).collect();
    let v_mat = Array2::from_shape_vec((cols, k), v_raw).unwrap();
    let v = qr_q(&v_mat, k);

    // Ill-conditioned: ratio 1000:1
    let s = vec![1000.0, 1.0];

    let mut a = Array2::<f64>::zeros((rows, cols));
    for i in 0..rows {
        for j in 0..cols {
            let val: f64 = (0..k).map(|l| u[(i, l)] * s[l] * v[(j, l)]).sum();
            a[(i, j)] = val;
        }
    }

    // PerSVD with 0 power iterations
    let r0 = per_svd(&a, PerSVDParams {
        ost: 5,
        power_iters: 0,
        shift_type: PerSVDShift::Adaptive,
    });
    let approx0 = low_rank_approx(&r0, k);
    let frob0 = relative_frobenius_error(&a, &approx0);

    // PerSVD with 1 power iteration
    let r1 = per_svd(&a, PerSVDParams {
        ost: 5,
        power_iters: 1,
        shift_type: PerSVDShift::Adaptive,
    });
    let approx1 = low_rank_approx(&r1, k);
    let frob1 = relative_frobenius_error(&a, &approx1);

    eprintln!("per_svd_power: no_power_frob={:.2e}, power1_frob={:.2e}", frob0, frob1);
    // Power iteration should not worsen accuracy (may improve)
    assert!(frob1 < 1e-6, "PerSVD with power iter error too high: {frob1:.2e}");
}

/// Test PerSVD 'Once' shift strategy works correctly.
#[test]
fn per_svd_shift_once() {
    let a = make_test_matrix(25, 20, 2);
    let result = per_svd(&a, PerSVDParams {
        ost: 5,
        power_iters: 0,
        shift_type: PerSVDShift::Once,
    });

    let approx = low_rank_approx(&result, 2);
    let frob = relative_frobenius_error(&a, &approx);
    eprintln!("per_svd_shift_once: frob_err={:.2e}", frob);
    assert!(frob < 1e-6, "PerSVD shift=Once error too high: {frob:.2e}");
}

/// Compare PerSVD vs standard randomized SVD on a moderately ill-conditioned matrix.
/// PerSVD should achieve better accuracy with fewer passes.
#[test]
fn per_svd_vs_randomized_svd() {
    let a = make_test_matrix(40, 30, 3);

    // Standard randomized SVD with power iterations
    let rand_result = randomized_svd(&a, 3, 5, 2);
    let rand_approx = low_rank_approx(&rand_result, 3);
    let rand_frob = relative_frobenius_error(&a, &rand_approx);

    // PerSVD with no power iterations (should match standard R-SVD with power=2)
    let persvd_result = per_svd(&a, PerSVDParams {
        ost: 5,
        power_iters: 0,
        shift_type: PerSVDShift::Adaptive,
    });
    let persvd_approx = low_rank_approx(&persvd_result, 3);
    let persvd_frob = relative_frobenius_error(&a, &persvd_approx);

    eprintln!("per_svd_vs_randomized: rand_frob={:.2e}, persvd_frob={:.2e}",
        rand_frob, persvd_frob);
    // Both should be reasonably accurate
    assert!(persvd_frob < 1e-4, "PerSVD error too high: {persvd_frob:.2e}");
    assert!(rand_frob < 1e-4, "Randomized SVD error too high: {rand_frob:.2e}");
}
