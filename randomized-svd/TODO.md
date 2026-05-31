# Randomized SVD — Plan & Status

## Specs (from `specs.txt`)

- Build randomized SVD from scratch in Rust
- Priority 1: Correctness
- Priority 2: Working code
- Priority 3: Numerical accuracy improvements
- Explore high-accuracy inner SVD (twisted factorization, Fernando)
- Compare f32, f64, and 2xf64 (quad) precision; Kahan summation
- CI via `ci.sh`, commit often
- Save status/todos to repo

## Architecture

```
randomized-svd/
├── Cargo.toml
├── ci.sh               — CI script (build + test)
├── lakefile.toml        — Lean4 project config
├── lean-toolchain       — Lean4 version (v4.29.0)
├── src/
│   ├── lib.rs          — public API
│   ├── svd.rs          — randomized SVD algorithm
│   ├── matrix.rs       — QR decomposition (MGS + re-orthogonalization)
│   ├── eigen.rs        — symmetric eigendecomposition (Jacobi)
│   └── error.rs        — error metrics
├── tests/
│   └── integration.rs  — correctness tests (9 tests, all passing)
└── lean/
    ├── RandomizedSVD.lean          — main import file
    ├── RandomizedSVD/
    │   ├── Matrix.lean             — matrix operations, norms
    │   ├── QR.lean                 — MGS QR + re-orthogonalization
    │   ├── Eigen.lean              — Jacobi eigenvalue algorithm
    │   ├── RandomizedSVD.lean      — main algorithm + low-rank approx
    │   ├── LowRankApprox.lean      — rank-k reconstruction, Eckart-Young
    │   └── AccuracyBounds.lean     — probabilistic error bounds
    ├── Tests/
    │   ├── Main.lean               — test suite
    │   └── TestMatrix.lean         — test matrix generators
    └── Fuzz/
        └── Main.lean               — fuzz testing (TODO)
```

## Algorithm (Halko–Martinsson–Tropp 2011)

1. Random Gaussian probe Ω ∈ ℝ^{n×p}, p = k + ost
2. Subspace iteration: Y = AΩ (optionally power-iterate)
3. QR (Modified Gram-Schmidt + re-orthogonalization) → orthonormal Q
4. Project: B = Q^T A
5. SVD of B via eigen-decomposition of B B^T (Jacobi algorithm)
6. Map back: U = Q U_B, S = Σ, V^T
7. Low-rank approximation: A ≈ U_k diag(S_k) V_k^T

## TODO

### Phase 1: Core ✅ DONE
- [x] Project skeleton (Cargo.toml, lib.rs, modules)
- [x] QR decomposition (Modified Gram-Schmidt + re-orthogonalization)
- [x] Symmetric eigendecomposition (Jacobi algorithm)
- [x] Randomized SVD algorithm
- [x] Low-rank approximation
- [x] Error metrics (Frobenius, spectral)
- [x] Fix compilation errors (ndarray 0.15 compatibility)
- [x] Fix matrix dimension mismatches in QR and SVD
- [x] All 9 integration tests passing (CI clean)

### Phase 2: Lean4 Formalization 🔄 IN PROGRESS
- [x] Project setup (lakefile.toml, lean-toolchain)
- [x] Matrix operations (multiplication, transpose, norms)
- [x] QR decomposition formalization (MGS + re-orthogonalization)
- [x] Jacobi eigenvalue algorithm formalization
- [x] Randomized SVD algorithm formalization
- [x] Low-rank approximation formalization
- [x] Accuracy bounds formalization
- [x] Test suite skeleton
- [ ] Proofs for Q orthogonality (replace axioms with proofs)
- [ ] Proofs for decomposition correctness (A = QR)
- [ ] Proofs for spectral theorem (A = V Λ V^T)
- [ ] Proofs for randomized SVD error bounds
- [ ] Proofs for Eckart-Young-Mirsky theorem
- [ ] Fuzz testing framework

### Phase 3: Experiments 📝
- [ ] f32 vs f64 comparison
- [ ] Power iterations benchmark
- [ ] Oversampling study

### Phase 4: Accuracy Improvements 📝
- [ ] Kahan summation experiments
- [ ] Quadruple precision (2xf64 high-low representation)
- [ ] Compare with standard SVD on ill-conditioned matrices

### Phase 5: Advanced SVD 📝
- [x] Research: PerSVD (Feng, Yu, Xie) — pass-efficient with shifted power iteration
      - Paper: "Pass-efficient randomized SVD with boosted accuracy", ECML PKDD 2022
      - Code: https://github.com/THU-numbda/PerSVD
      - Key idea: shifted power iteration with adaptive shift alpha = (alpha + sigma_min)/2
      - Uses svd(A^T*A*Q - alpha*Q) instead of qr(A^T*A*Q)
      - Achieves 3-4 orders of magnitude error reduction
      - TODO: Full implementation requires correct economy SVD decomposition
- [ ] Research: twisted factorization / Fernando's method
- [ ] Implement high-accuracy bidiagonal SVD kernel
- [ ] Replace inner SVD with high-accuracy variant
- [ ] Implement full PerSVD with shifted power iteration (currently wraps randomized_svd)

### Phase 6: Polish 📝
- [ ] f32 API variant
- [ ] Documentation / examples
- [ ] Benchmarking
- [ ] Fuzz testing against known matrices

## Status

| Phase | Status |
|-------|--------|
| Core (Rust) | ✅ Complete (9 tests passing, CI clean) |
| Lean4 Formalization | 🔄 Skeleton complete, all theorems as axioms |
| Experiments | 📝 Planned |
| Accuracy | 📝 Planned |
| Advanced SVD | 📝 Planned |

## Key Bugs Fixed

- **2026-05-30/31**: QR decomposition (MGS) produced non-orthonormal columns for rank-deficient matrices (e.g., Y = AΩ where A is rank-3 but we asked for 8 columns). Fixed by adding a **re-orthogonalization pass** after MGS.
- **2026-05-30**: Test matrix singular values were `[1, 0.1, 0.01]` instead of `[100, 10, 1]` due to `10.0_f64.powi(-0)` = 1.0. Fixed formula.
- **2026-05-30**: Replaced broken QR iteration eigenvalue solver with Jacobi eigenvalue algorithm.
- **2026-05-30**: Fixed ndarray 0.15 compatibility (no `.abs()`, no `.linspace()`).

## PerSVD (Feng, Yu, Xie) — Pass-efficient Randomized SVD

**Paper:** "Pass-efficient randomized SVD with boosted accuracy"
**Key innovations:**
- Reduces passes in basic randomized SVD by half (3-4 vs 5+)
- Uses **shifted power iteration**: (A - σI)Ω instead of AΩ
- Dynamic shift scheme for improving accuracy
- **3-4 orders of magnitude** error reduction

**Planned implementation:** Phase 5, after core is stable.

## Running CI

```bash
cd /home/pc/work/numerical-algorithms/randomized-svd
ci.sh   # or: cargo build && cargo test
```

## Running Lean4

```bash
cd /home/pc/work/numerical-algorithms/randomized-svd/lean
lake build
```
