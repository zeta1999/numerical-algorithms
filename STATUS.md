# Project Status

## nr1: LU Decomposition

**Algorithm:** Doolittle LU with partial pivoting

### Lean4 (`nr1/lean/`)
- Library `LUDecomp` builds
- 14 unit tests pass (5 exact ℚ + 9 float)
- 3500 fuzz tests pass (sizes 2-20 + Hilbert 2-8)
- Sensitivity analysis CSV across 4 sizes × 7 condition numbers

### F* (`nr1/fstar/`)
- 5 modules verified by Z3: Matrix, Decompose, Proofs, Tests, Fuzz
- Fraction-free integer arithmetic

### Proof state
- **Proved (Lean4):** L lower triangular, L unit diagonal
- **Proved (F\*):** identity matrix properties, iabs properties, zero_vec/mat
- **Axiomatized:** U upper triangular, PA=LU, solve correct, det via LU
  (all verified empirically by tests + fuzzing)
- **Admitted (F\*):** find_pivot bounds, swap_rows involution

---

## nr2: QR Decomposition

**Algorithm:** Modified Gram-Schmidt

### Lean4 (`nr2/lean/`)
- Library `QRDecomp` builds
- 14 unit tests pass (5 exact ℚ + 9 float)
- 3500 fuzz tests pass (sizes 2-20 + Hilbert 2-8)
- Sensitivity analysis CSV with QR-specific metrics (orthogonality loss, reconstruction error)

### F* (`nr2/fstar/`)
- 5 modules verified by Z3: Matrix, Decompose, Proofs, Tests, Fuzz
- Fraction-free integer arithmetic (unnormalized MGS)

### Proof state
- **Proved (Lean4):** R upper triangular, R unit diagonal
- **Proved (F\*):** identity matrix properties, iabs properties, zero_vec/mat
- **Axiomatized:** A=QR, Q columns orthogonal, solve correct
  (all verified empirically by tests + fuzzing)
- **Admitted (F\*):** dot_product self non-negative, dot_product commutative

---

## How to run

```bash
# nr1 (LU)
cd nr1 && bash run.sh

# nr2 (QR)
cd nr2 && bash run.sh
```

Lean4 requires `lake` (matches `lean-toolchain` file).
F* requires `fstar.exe` and `z3-4.13.3` on PATH.

---

## Open todos

### Compatibility / cleanup
1. **`xxx.txt`** at repo root — scratch file, can be deleted
2. **F\* `.checked` cache warnings** — harmless, could suppress via `--cache_dir` flag in Makefiles

### Formal verification gaps
3. **Lean4 algorithmic correctness axioms** (both nr1 and nr2):
   - `U_upper_triangular` / `R_upper_triangular` (R done in nr2)
   - `PA_eq_LU` / `A_eq_QR`
   - `Q_columns_orthogonal` (nr2)
   - `solve_correct`
   - `det_via_LU`
   
   These require induction over the full recursive execution of
   `luDecomposeAux` / `qrDecomposeAux`. Substantial effort (~100s lines each).
   
4. **F\* inline let-rec admits**:
   - `find_pivot_ge_start`, `find_pivot_valid` (nr1)
   - `dot_product_self_nonneg`, `dot_product_comm` (nr2)
   
   These are blocked by F*'s inability to reference closures nested inside
   function bodies. Fix would require refactoring the functions to use
   top-level recursive helpers instead of `let rec` inside.

5. **F\* `swap_rows_involution`** (nr1) — admitted due to extensional
   sequence equality; would need additional FStar.Seq lemmas.

### Possible enhancements
6. **Alternative QR algorithms**: Householder reflections or Givens rotations
   would give better orthogonality preservation for ill-conditioned matrices.
   (Current MGS: orthogonality loss ~ κ(A) · ε_mach)
7. **Rank-revealing decomposition**: detect numerical rank deficiency.
8. **Rectangular matrices**: current implementation is square-only.
9. **nr3 and beyond**: SVD, Cholesky, eigendecomposition, etc.
