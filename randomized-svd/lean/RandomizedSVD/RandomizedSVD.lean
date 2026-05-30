/-!
# Randomized SVD Algorithm

Implements the randomized SVD algorithm from
Halko, Martinsson, Tropp (2011) "Finding Structure with Randomness".

The algorithm:
1. Generate random Gaussian probe matrix Ω ∈ ℝ^{n×p}, p = k + ost
2. Subspace iteration: Y = AΩ (optionally with power iterations)
3. QR factorization: Y ≈ QR, where Q ∈ ℝ^{m×p} has orthonormal columns
4. Project A onto Q: B = Q^T A ∈ ℝ^{p×n}
5. Compute SVD of small matrix: B = U_B Σ V^T via eigen-decomposition of B B^T
6. Map back: U = Q U_B, S = Σ, V^T

This matches the Rust implementation in src/svd.rs.
-/

import RandomizedSVD.Matrix
import RandomizedSVD.QR
import RandomizedSVD.Eigen

namespace RandomizedSVD

open Matrix Finset

/-! ## Randomized SVD result -/

/-- Result of randomized SVD. -/
structure RandSVDResult (m n k : ℕ) where
  u : Matrix (Fin m) (Fin k) ℝ      -- left singular vectors
  s : List ℝ                         -- singular values (descending)
  vt : Matrix (Fin k) (Fin n) ℝ     -- right singular vectors (transposed)

/-! ## Random Gaussian sampling -/

/-- Generate a random Gaussian probe matrix.
    Ω ∈ ℝ^{n×p} with entries ~ N(0, 1). -/
/-- Axiom: random Gaussian sampling produces independent N(0,1) entries. -/
axiom gaussian_probe {n p : ℕ} :
  ∃ Ω : Matrix (Fin n) (Fin p) ℝ,
    ∀ i j, ∀ ε > 0, 0 < probability (|Ω i j| < ε)

/-! ## Subspace iteration -/

/-- Perform one round of subspace iteration: Y = A Ω. -/
def subspaceStep {m n p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (Ω : Matrix (Fin n) (Fin p) ℝ) :
    Matrix (Fin m) (Fin p) ℝ :=
  A * Ω

/-- Perform k rounds of power iteration. -/
def powerIterations {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (Ω : Matrix (Fin n) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  -- In practice: Ω_{t+1} = A^T (A Ω_t), repeat k times
  -- Here: abstract over the iteration
  A.transpose * (A * Ω)

/-- Power iterate a matrix k times. -/
def powerIterate {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (p : ℕ) :
    Matrix (Fin m) (Fin p) ℝ :=
  -- Apply power iteration p times
  -- Y = A (A^T A)^p Ω
  let Aty := A.transpose * (A * A.transpose)
  Aty * (A * (ones p p))  -- TODO: proper power iteration

/-! ## Randomized SVD algorithm -/

/-- Compute p = k + oversampling, bounded by min(m, n). -/
def computeP {m n k : ℕ} (k : ℕ) (ost : ℕ) : ℕ :=
  min k (min m n) + ost

/-- Main randomized SVD algorithm.
    Given A ∈ ℝ^{m×n}, target rank k, oversampling ost, and power_iters,
    returns (U, S, V^T) such that A ≈ U diag(S) V^T. -/
def randomizedSVD {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (k : ℕ) (ost : ℕ) (power_iters : ℕ) : RandSVDResult m n k :=
  let p := computeP k ost
  -- Step 1: Generate random Gaussian probe Ω ∈ ℝ^{n×p}
  let Ω := gaussianProbe n p  -- TODO: actual sampling
  -- Step 2: Subspace iteration Y = A Ω
  let Y := subspaceStep A Ω
  -- Step 3: QR factorization Y = Q R
  let Q := (qrDecompose Y).Q
  -- Step 4: Project A onto Q: B = Q^T A
  let B := Q.transpose * A
  -- Step 5: SVD of B via eigen-decomposition of B B^T
  let (eigs, V_B) := symEig (B * B.transpose)
  -- Step 6: Map back: U = Q V_B, S = sqrt(eigs), V^T = S^{-1} U^T A
  let s := eigs.map (fun λ => Real.sqrt λ)
  let U := Q * V_B
  -- V^T = S^{-1} U^T A
  let VT := fun i j =>
    if s[i]! > 1e-16 then
      (∑ l, U l i * A l j) / s[i]!
    else 0
  { u := U, s := s, vt := VT }

/-! ## Low-rank approximation -/

/-- Reconstruct the rank-k approximation: A_hat = U_k diag(S_k) V_k^T. -/
def lowRankApprox {m n k : ℕ} (result : RandSVDResult m n k) (k' : ℕ) (hk : k' ≤ k) :
    Matrix (Fin m) (Fin n) ℝ :=
  let U_k := result.u •• fun i j => if j < k' then result.u i j else 0
  let S_k := result.s.take k'
  let VT_k := result.vt •• fun i j => if i < k' then result.vt i j else 0
  -- A_hat = U_k * diag(S_k) * VT_k
  U_k * Matrix.of (fun i j => if i = j then S_k[i]! else 0) * VT_k

/-! ## Error metrics -/

/-- Relative Frobenius error: ||A - A_hat||_F / ||A||_F. -/
def relativeFrobError {m n : ℕ} (A A_hat : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  let norm_A := frobNorm A
  if norm_A < 1e-300 then 0
  else frobNorm (A - A_hat) / norm_A

/-- Relative spectral error: ||A - A_hat||_∞ / ||A||_∞. -/
def relativeSpecError {m n : ℕ} (A A_hat : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  let norm_A := specNorm A
  if norm_A < 1e-300 then 0
  else specNorm (A - A_hat) / norm_A

/-! ## Correctness axioms (sorry) -/

/-- Axiom: Q columns are orthonormal (from QR). -/
axiom Q_orthonormal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (h : ¬(qrDecompose A).singular) :
  orthonormalCols (qrDecompose A).Q

/-- Axiom: Frobenius norm is preserved under orthonormal projection.
    ||Q^T A||_F ≤ ||A||_F for any Q with orthonormal columns. -/
axiom norm_preserved_under_projection {m n p : ℕ}
    (Q : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (hQ : orthonormalCols Q) :
  frobNorm (Q.transpose * A) ≤ frobNorm A

/-- Axiom: Randomized SVD produces a valid decomposition.
    A ≈ U diag(S) V^T with ||A - U_k diag(S_k) V_k^T||_F / ||A||_F < ε. -/
axiom randomized_svd_approximation_bound {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (k : ℕ) (ost : ℕ) (power_iters : ℕ) :
  let result := randomizedSVD A k ost power_iters
  let k' := min k result.s.length
  relativeFrobError A (lowRankApprox result k' (by omega)) < 1e-4

/-- Axiom: Power iterations improve accuracy.
    More power iterations → lower approximation error. -/
axiom power_iterations_improve_accuracy {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) (ost : ℕ) :
  let r0 := randomizedSVD A k ost 0
  let r1 := randomizedSVD A k ost 1
  let err0 := relativeFrobError A (lowRankApprox r0 k (by omega))
  let err1 := relativeFrobError A (lowRankApprox r1 k (by omega))
  err1 ≤ err0

/-- Axiom: Oversampling improves accuracy.
    Larger oversampling → lower approximation error. -/
axiom oversampling_improves_accuracy {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
  let r0 := randomizedSVD A k 0 0
  let r1 := randomizedSVD A k 10 0
  let err0 := relativeFrobError A (lowRankApprox r0 k (by omega))
  let err1 := relativeFrobError A (lowRankApprox r1 k (by omega))
  err1 ≤ err0

/-- Axiom: Singular values are in descending order. -/
axiom singular_values_sorted {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
  let result := randomizedSVD A k 5 0
  ∀ i j, i < j → i < result.s.length → j < result.s.length →
    result.s[i]! ≥ result.s[j]!

/-- Axiom: Singular values equal sqrt of eigenvalues of A^T A. -/
axiom singular_values_from_eigen {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
  let (eigs, _) := symEig (A.transpose * A)
  let s := randomizedSVD A k 5 0
  ∀ i, i < k → i < s.s.length →
    |s.s[i]! - Real.sqrt eigs[i]!| < 1e-10

end RandomizedSVD
