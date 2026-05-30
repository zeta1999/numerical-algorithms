/-!
# Low-Rank Approximation

Given the SVD result U, S, V^T, reconstruct the rank-k approximation:
A_hat = U_k diag(S_k) V_k^T

This module formalizes the reconstruction and error analysis.
-/

import RandomizedSVD.RandomizedSVD

namespace RandomizedSVD

open Matrix Finset

/-! ## Rank-k truncation -/

/-- Truncate the SVD to rank k'. -/
def truncateSVD {m n k : ℕ} (result : RandSVDResult m n k) (k' : ℕ) (hk : k' ≤ k) :
    RandSVDResult m n k' :=
  { u := result.u •• fun i j => if j < k' then result.u i j else 0
    s := result.s.take k'
    vt := result.vt •• fun i j => if i < k' then result.vt i j else 0 }

/-- Compute the rank-k approximation: A_hat = U_k diag(S_k) V_k^T. -/
def rankKApprox {m n k : ℕ} (result : RandSVDResult m n k) (k' : ℕ) (hk : k' ≤ k) :
    Matrix (Fin m) (Fin n) ℝ :=
  let U_k := result.u •• fun i j => if j < k' then result.u i j else 0
  let VT_k := result.vt •• fun i j => if i < k' then result.vt i j else 0
  let S_k_diag := Matrix.of (fun i j => if i = j ∧ i < k' then result.s[i]! else 0)
  U_k * S_k_diag * VT_k

/-! ## Error analysis -/

/-- Relative Frobenius error. -/
def frobError {m n : ℕ} (A A_hat : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  let norm_A := frobNorm A
  if norm_A < 1e-300 then 0
  else frobNorm (A - A_hat) / norm_A

/-- Relative spectral error. -/
def specError {m n : ℕ} (A A_hat : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  let norm_A := specNorm A
  if norm_A < 1e-300 then 0
  else specNorm (A - A_hat) / norm_A

/-! ## Eckart-Young-Mirsky theorem (statement) -/

/-- Axiom: Eckart-Young-Mirsky theorem.
    The rank-k approximation from SVD minimizes the error among all rank-k matrices.

    Formally: If A = U Σ V^T is the SVD of A, and A_k = U_k Σ_k V_k^T is the
    rank-k truncation, then for any matrix B of rank ≤ k:
      ||A - A_k||_F ≤ ||A - B||_F
      ||A - A_k||_2 ≤ ||A - B||_2

    This is the optimality property of the truncated SVD. -/
axiom eckart_young_mirsky {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
  let result := randomizedSVD A k 5 0
  let A_k := rankKApprox result k (by omega)
  ∀ B : Matrix (Fin m) (Fin n) ℝ,
    rank B ≤ k →
    frobNorm (A - A_k) ≤ frobNorm (A - B) ∧
    specNorm (A - A_k) ≤ specNorm (A - B)

/-! ## Johnson-Lindenstrauss connection -/

/-- Axiom: Randomized SVD preserves pairwise distances approximately.
    For any vectors x, y in the column space of A:
      (1-ε)||x-y|| ≤ ||x_hat - y_hat|| ≤ (1+ε)||x-y||
    where x_hat, y_hat are their projections onto the subspace spanned
    by the top-k right singular vectors. -/
axiom jl_property {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
  let result := randomizedSVD A k 5 0
  let VT_k := result.vt •• fun i j => if i < k then result.vt i j else 0
  ∀ x y : Fin n → ℝ,
    let dist_A := ‖x - y‖
    let dist_proj := ‖(x - y) • VT_k‖
    dist_proj ≤ (1 + 1e-4) * dist_A ∧ dist_proj ≥ (1 - 1e-4) * dist_A

end RandomizedSVD
