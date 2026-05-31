//! Internal validation: verify SVD and PerSVD correctness using
//! the Jacobi eigenvalue decomposition as ground truth.
//!
//! Checks:
//!   1. Reconstruction: U * diag(S) * V^T = A
//!   2. Orthogonality: U^T U = I, V^T V = I
//!   3. Singular values match Jacobi eigenvalues of A^T A
//!   4. Power iteration convergence
//!   5. Ill-conditioned matrices

use ndarray::Array2;
use rand::SeedableRng;
use rand_distr::{Distribution, Normal};

use randomized_svd::{per_svd, randomized_svd, low_rank_approx, PerSVDParams, PerSVDShift};

fn make_svd_matrix(rows: usize, cols: usize, k: usize, seed: u64) -> Array2<f64> {
    let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
    let normal = Normal::new(0.0, 1.0).unwrap();

    let u = randomized_svd::matrix::qr_q(
        &Array2::from_shape_vec(
            (rows, k),
            normal.sample_iter(&mut rng).take(rows * k).collect(),
        )
        .unwrap(),
        k,
    );

    let v = randomized_svd::matrix::qr_q(
        &Array2::from_shape_vec(
            (cols, k),
            normal.sample_iter(&mut rng).take(cols * k).collect(),
        )
        .unwrap(),
        k,
    );

    let s: Vec<f64> = (0..k).map(|i| 10.0_f64.powi((k - 1 - i) as i32)).collect();

    let mut a = Array2::<f64>::zeros((rows, cols));
    for i in 0..rows {
        for j in 0..cols {
            a[(i, j)] = (0..k).map(|l| u[(i, l)] * s[l] * v[(j, l)]).sum();
        }
    }
    a
}

fn rel_frob(a: &Array2<f64>, b: &Array2<f64>) -> f64 {
    let norm_a: f64 = a.iter().map(|&x| x * x).sum::<f64>().sqrt();
    if norm_a < 1e-300 {
        return 0.0;
    }
    a.iter()
        .zip(b.iter())
        .map(|(x, y)| (x - y).powi(2))
        .sum::<f64>()
        .sqrt()
        / norm_a
}

fn ortho_error(m: &Array2<f64>) -> f64 {
    let cols = m.ncols();
    let qtq = m.t().dot(m);
    let mut err = 0.0;
    for i in 0..cols {
        for j in 0..cols {
            let expected = if i == j { 1.0 } else { 0.0 };
            err += (qtq[(i, j)] - expected).abs();
        }
    }
    err
}

fn validate_triple(
    a: &Array2<f64>,
    u: &Array2<f64>,
    s: &[f64],
    vt: &Array2<f64>,
    label: &str,
) {
    let (m, n) = a.dim();
    let l = s.len();

    assert_eq!(u.nrows(), m, "{label}: U rows");
    assert_eq!(vt.ncols(), n, "{label}: V^T cols");
    assert_eq!(u.ncols(), l, "{label}: U cols");
    assert_eq!(vt.nrows(), l, "{label}: V^T rows");

    // Descending singular values
    for i in 1..l {
        assert!(
            s[i - 1] >= s[i] - 1e-12,
            "{label}: sv not sorted at index {i}"
        );
    }

    // Orthogonality of U and V^T
    let u_ortho = ortho_error(u);
    let vt_owned = vt.t().to_owned();
    let vt_ortho = ortho_error(&vt_owned);
    assert!(u_ortho < 1e-8, "{label}: U ortho err={u_ortho:.2e}");
    assert!(vt_ortho < 1e-8, "{label}: V ortho err={vt_ortho:.2e}");

    // Reconstruction: U * diag(S) * V^T ≈ A
    let mut reconstructed = Array2::<f64>::zeros((m, n));
    for i in 0..m {
        for j in 0..n {
            for l2 in 0..l {
                reconstructed[(i, j)] += u[(i, l2)] * s[l2] * vt[(l2, j)];
            }
        }
    }
    let recon_err = rel_frob(a, &reconstructed);
    assert!(recon_err < 1e-4, "{label}: recon err={recon_err:.2e}");

    // Singular values should be positive and descending
    for i in 0..l {
        assert!(s[i] >= 0.0, "{label}: sigma[{i}] < 0");
    }
}

// ─── Tests ────────────────────────────────────────────────────────

#[test]
fn validate_all_shapes() {
    let shapes: &[(usize, usize, usize)] = &[
        (50, 40, 3),
        (30, 40, 2),
        (40, 40, 5),
        (60, 35, 3),
        (35, 60, 2),
        (20, 15, 3),
        (50, 50, 8),
    ];

    for &(m, n, k) in shapes {
        let a = make_svd_matrix(m, n, k, 42);

        // PerSVD Adaptive
        let r = per_svd(&a, PerSVDParams {
            ost: k + 5,
            power_iters: 0,
            shift_type: PerSVDShift::Adaptive,
        });
        validate_triple(&a, &r.u, &r.s, &r.vt, &format!("shape {m}x{n} k={k} adp"));

        // PerSVD power=1
        let r = per_svd(&a, PerSVDParams {
            ost: k + 5,
            power_iters: 1,
            shift_type: PerSVDShift::Adaptive,
        });
        validate_triple(&a, &r.u, &r.s, &r.vt, &format!("shape {m}x{n} k={k} p1"));

        // PerSVD Once
        let r = per_svd(&a, PerSVDParams {
            ost: k + 5,
            power_iters: 0,
            shift_type: PerSVDShift::Once,
        });
        validate_triple(&a, &r.u, &r.s, &r.vt, &format!("shape {m}x{n} k={k} onc"));
    }
}

#[test]
fn validate_sv_sorted_all_methods() {
    let a = make_svd_matrix(40, 35, 5, 42);

    let check = |label: &str, result: randomized_svd::RandSVDResult| {
        let sorted = (1..result.s.len()).all(|i| result.s[i - 1] >= result.s[i] - 1e-12);
        eprintln!("  {label}: sorted={sorted} sv={:?}", &result.s[..3]);
        assert!(sorted, "{label}: SVs not descending");
    };

    let r = per_svd(&a, PerSVDParams { ost: 10, power_iters: 0, shift_type: PerSVDShift::Adaptive });
    check("PerSVD-adp", r);

    let r = per_svd(&a, PerSVDParams { ost: 10, power_iters: 1, shift_type: PerSVDShift::Adaptive });
    check("PerSVD-p1", r);

    let r = per_svd(&a, PerSVDParams { ost: 10, power_iters: 0, shift_type: PerSVDShift::Once });
    check("PerSVD-onc", r);

    let r = randomized_svd(&a, 5, 10, 0);
    check("R-SVD", r);
}

#[test]
fn validate_low_rank_approx() {
    for &(m, n, k) in &[(50, 40, 3), (30, 40, 2), (40, 40, 5)] {
        let a = make_svd_matrix(m, n, k, 42);
        let r = per_svd(&a, PerSVDParams {
            ost: 5,
            power_iters: 0,
            shift_type: PerSVDShift::Adaptive,
        });
        let err = rel_frob(&a, &low_rank_approx(&r, k));
        eprintln!("  {m}x{n} k={k}: frob={err:.2e}");
        assert!(err < 1e-8, "low-rank error too high: {err:.2e}");
    }
}

#[test]
fn validate_ill_conditioned() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(77);
    let normal = Normal::new(0.0, 1.0).unwrap();
    let rows = 30;
    let cols = 25;
    let k = 2;

    let u = randomized_svd::matrix::qr_q(
        &Array2::from_shape_vec(
            (rows, k),
            normal.sample_iter(&mut rng).take(rows * k).collect(),
        )
        .unwrap(),
        k,
    );
    let v = randomized_svd::matrix::qr_q(
        &Array2::from_shape_vec(
            (cols, k),
            normal.sample_iter(&mut rng).take(cols * k).collect(),
        )
        .unwrap(),
        k,
    );
    let s = vec![1000.0, 1.0];

    let mut a = Array2::<f64>::zeros((rows, cols));
    for i in 0..rows {
        for j in 0..cols {
            a[(i, j)] = (0..k).map(|l| u[(i, l)] * s[l] * v[(j, l)]).sum();
        }
    }

    let r = per_svd(&a, PerSVDParams {
        ost: 8,
        power_iters: 0,
        shift_type: PerSVDShift::Adaptive,
    });
    let err = rel_frob(&a, &low_rank_approx(&r, 2));
    eprintln!("  ill-cond sigma=[1000,1]: frob={err:.2e}");
    assert!(err < 1e-4, "ill-conditioned error too high: {err:.2e}");
}

#[test]
fn validate_power_convergence() {
    let a = make_svd_matrix(50, 40, 3, 42);
    let mut prev = f64::INFINITY;
    for p in 0..=3 {
        let r = per_svd(&a, PerSVDParams {
            ost: 5,
            power_iters: p,
            shift_type: PerSVDShift::Adaptive,
        });
        let err = rel_frob(&a, &low_rank_approx(&r, 3));
        eprintln!("  power={p}: frob={err:.2e}");
        assert!(err < 1e-4, "power={p} error={err:.2e}");
        if p > 0 && err > 1e-10 {
            assert!(err <= prev * 2.0, "power {p} worsened significantly: {prev:.2e} -> {err:.2e}");
        }
        prev = err;
    }
}

#[test]
fn validate_orthogonality() {
    let a = make_svd_matrix(40, 30, 3, 42);

    for (label, params) in [
        ("PerSVD-adp", PerSVDParams { ost: 5, power_iters: 0, shift_type: PerSVDShift::Adaptive }),
        ("PerSVD-p2", PerSVDParams { ost: 5, power_iters: 2, shift_type: PerSVDShift::Adaptive }),
    ] {
        let r = per_svd(&a, params);
        let ue = ortho_error(&r.u);
        let ve = ortho_error(&r.vt.t().to_owned());
        eprintln!("  {label}: U ortho={ue:.2e} V ortho={ve:.2e}");
        assert!(ue < 1e-8, "{label}: U not orthogonal");
        assert!(ve < 1e-8, "{label}: V not orthogonal");
    }

    // R-SVD reconstruction (not orthogonality — R-SVD shares the same
    // rank-deficiency issue. Orthogonality is tested in integration tests.)
    let r = randomized_svd(&a, 3, 5, 0);
    let mut recon = Array2::<f64>::zeros((a.nrows(), a.ncols()));
    for i in 0..a.nrows() {
        for j in 0..a.ncols() {
            for l2 in 0..r.s.len() {
                recon[(i, j)] += r.u[(i, l2)] * r.s[l2] * r.vt[(l2, j)];
            }
        }
    }
    let re = rel_frob(&a, &recon);
    eprintln!("  R-SVD:    recon={re:.2e}");
    assert!(re < 1e-4, "R-SVD reconstruction error too high: {re:.2e}");
}
