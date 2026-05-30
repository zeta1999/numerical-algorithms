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
├── src/
│   ├── lib.rs          — public API
│   ├── svd.rs          — randomized SVD algorithm
│   ├── matrix.rs       — QR decomposition (MGS + re-orthogonalization)
│   ├── eigen.rs        — symmetric eigendecomposition (Jacobi)
│   └── error.rs        — error metrics
└── tests/
    └── integration.rs  — correctness tests (9 tests, all passing)
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

### Phase 2: Experiments 📝
- [ ] f32 vs f64 comparison
- [ ] Power iterations benchmark
- [ ] Oversampling study

### Phase 3: Accuracy Improvements 📝
- [ ] Kahan summation experiments
- [ ] Quadruple precision (2xf64 high-low representation)
- [ ] Compare with standard SVD on ill-conditioned matrices

### Phase 4: Advanced SVD 📝
- [ ] Research: twisted factorization / Fernando's method
- [ ] Implement high-accuracy bidiagonal SVD kernel
- [ ] Replace inner SVD with high-accuracy variant

### Phase 5: Polish 📝
- [ ] f32 API variant
- [ ] Documentation / examples
- [ ] Benchmarking
- [ ] Fuzz testing against known matrices

## Status

| Phase | Status |
|-------|--------|
| Core | ✅ Complete (9 tests passing, CI clean) |
| Experiments | 📝 Planned |
| Accuracy | 📝 Planned |
| Advanced SVD | 📝 Planned |

## Key Bugs Fixed

- **2026-05-30/31**: QR decomposition (MGS) produced non-orthonormal columns for rank-deficient matrices (e.g., Y = AΩ where A is rank-3 but we asked for 8 columns). Fixed by adding a **re-orthogonalization pass** after MGS.
- **2026-05-30**: Test matrix singular values were `[1, 0.1, 0.01]` instead of `[100, 10, 1]` due to `10.0_f64.powi(-0)` = 1.0. Fixed formula.
- **2026-05-30**: Replaced broken QR iteration eigenvalue solver with Jacobi eigenvalue algorithm.
- **2026-05-30**: Fixed ndarray 0.15 compatibility (no `.abs()`, no `.linspace()`).

## Running CI

```bash
cd /home/pc/work/numerical-algorithms/randomized-svd
ci.sh   # or: cargo build && cargo test
```
