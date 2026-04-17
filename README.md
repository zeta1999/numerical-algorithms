<p align="center">
  <img src="assets/logo.svg" alt="Numerical Algorithms" width="160"/>
</p>

<h1 align="center">Numerical Algorithms</h1>

<p align="center">
  <strong>Formally verified linear algebra — Lean4 & F*, proven and fuzzed.</strong>
</p>

<p align="center">
  <img src="https://img.shields.io/badge/status-WIP-yellow.svg" alt="WIP">
  <img src="https://img.shields.io/badge/Lean4-mathlib-blueviolet.svg" alt="Lean4">
  <img src="https://img.shields.io/badge/F*-Z3%20verified-orange.svg" alt="F*">
  <img src="https://img.shields.io/badge/tests-3500%2B%20fuzz-green.svg" alt="Tests">
  <img src="https://img.shields.io/badge/proofs-dual%20stack-lightgrey.svg" alt="Proofs">
</p>

> **⚠ Work in progress.** Several correctness properties are still axiomatized (verified by fuzzing, not proved). See [`STATUS.md`](STATUS.md) for the current proof state and open todos.

---

Dual-stack formal verification of classical numerical linear algebra.
Each algorithm is implemented **twice** — once in Lean4 (floats + exact ℚ) and once in F\* (fraction-free integer arithmetic) — with proofs, unit tests, fuzzing, and sensitivity analysis.

Built for correctness evidence that survives scrutiny: machine-checked proofs where feasible, axioms backed by thousands of randomized tests where proofs are still open.

## What's Inside

| Algorithm | Variant | Lean4 | F\* | Linear Solver | Sensitivity |
|---|---|:-:|:-:|:-:|:-:|
| **nr1 — LU** | Doolittle + partial pivoting | ℚ + Float | fraction-free ℤ | ✓ | ✓ |
| **nr2 — QR** | Modified Gram-Schmidt | ℚ + Float | fraction-free ℤ | ✓ | ✓ |

Each algorithm ships with:
- **Solver** — direct `Ax = b` via the decomposition
- **Sensitivity analysis** — forward/backward error vs. condition number κ(A)
- **Unit tests** — exact rationals and IEEE-754 doubles, side-by-side
- **Fuzz harness** — 3500 random matrices (sizes 2–20) plus Hilbert matrices (2–8)
- **Z3-verified F\* modules** — Matrix, Decompose, Proofs, Tests, Fuzz

## Proof State at a Glance

<table>
<tr><td>

**nr1 (LU)**

| Property | Status |
|---|:-:|
| `L` lower triangular | **proved** (Lean4) |
| `L` unit diagonal | **proved** (Lean4) |
| `U` upper triangular | axiom + fuzz |
| `PA = LU` | axiom + fuzz |
| `solve` correct | axiom + fuzz |
| `det` via LU | axiom + fuzz |

</td><td>

**nr2 (QR)**

| Property | Status |
|---|:-:|
| `R` upper triangular | **proved** (Lean4) |
| `R` unit diagonal | **proved** (Lean4) |
| `A = QR` | axiom + fuzz |
| `Q` columns orthogonal | axiom + fuzz |
| `solve` correct | axiom + fuzz |
| Matrix/iabs lemmas | **proved** (F\*) |

</td></tr>
</table>

> Axiomatized properties are verified empirically across thousands of random + pathological (Hilbert) matrices. See [`STATUS.md`](STATUS.md) for the full picture including admitted lemmas.

## Quick Start

```bash
# nr1 — LU decomposition
cd nr1 && bash run.sh

# nr2 — QR decomposition
cd nr2 && bash run.sh
```

Each `run.sh` builds the Lean4 library, runs unit + fuzz tests, produces a sensitivity CSV, then (if `fstar.exe` is on PATH) verifies the F\* modules with Z3.

## Requirements

- **Lean4** — `lake` matching the `lean-toolchain` file in each `*/lean/` directory (pulls mathlib)
- **F\*** — `fstar.exe` + `z3-4.13.3` on `PATH` (via `opam install fstar` or a release tarball)

## Sensitivity Analysis (LU, n=50)

Forward error scales with κ(A) · ε_machine, as theory predicts; backward error stays at machine precision across all condition numbers — confirming **backward stability** of LU with partial pivoting.

| Target κ | Actual κ | Mean Fwd Err | Max Fwd Err | Backward Err |
|---:|---:|---:|---:|---:|
| 1       | 1.00    | 0      | 0      | 0 |
| 1e4     | 4.22e4  | 0      | 0      | 0 |
| 1e8     | 3.54e8  | 0      | 0      | 0 |
| 1e10    | 3.23e10 | ~0     | ~0     | 0 |
| 1e12    | 3.22e12 | 1.3e-5 | 2.5e-5 | 0 |

Full tables across n = 5, 10, 20, 50 and QR-specific metrics (orthogonality loss, reconstruction error) in [`nr1/SENSITIVITY_ANALYSIS.md`](nr1/SENSITIVITY_ANALYSIS.md) and [`nr2/SENSITIVITY_ANALYSIS.md`](nr2/SENSITIVITY_ANALYSIS.md).

## Why Two Stacks?

| | Lean4 | F\* |
|---|---|---|
| **Arithmetic** | Exact ℚ + IEEE-754 Float (side-by-side) | Fraction-free integer (no rounding) |
| **Proof engine** | Tactic-based, mathlib ecosystem | SMT-backed (Z3), refinement types |
| **Good for** | Algebraic reasoning, mixed exact/float comparisons | Self-contained integer certificates, no real-number axioms |
| **Trade-off** | Float path not fully proved end-to-end | Integer MGS is unnormalized (scaled R) |

Running both stacks is the point: an axiom "proven by fuzzing" in one is usually **provable** in the other's model, and the shared surface of lemmas gives cross-stack cross-checking that a single tool cannot.

## Project Structure

```
nr1/                       # LU decomposition
  lean/                    #   Lean4 library + test/fuzz/sensitivity execs
  fstar/                   #   F* Matrix, Decompose, Proofs, Tests, Fuzz
  SENSITIVITY_ANALYSIS.md  #   Full κ(A) × n error tables
  run.sh                   #   Build + test + verify pipeline

nr2/                       # QR decomposition (same layout)

SPECS.md                   # Algorithm specs
STATUS.md                  # Per-algorithm proof state + open todos
```

## Open Work

1. **Lean4 axioms → theorems** — `U_upper_triangular`, `PA_eq_LU`, `A_eq_QR`, `solve_correct`, `det_via_LU`. Requires induction over the full recursive decomposition.
2. **F\* inline `let rec` admits** — `find_pivot_*`, `dot_product_self_nonneg`, `dot_product_comm`. Blocked by F\*'s closure-reference limitation; fix is refactor to top-level recursion.
3. **Algorithm extensions** — Householder / Givens QR for ill-conditioned matrices, rank-revealing decomposition, rectangular matrices, SVD / Cholesky / eigendecomposition (nr3+).

Full todo list and reasoning in [`STATUS.md`](STATUS.md).

## License

See individual subdirectories for license terms.
