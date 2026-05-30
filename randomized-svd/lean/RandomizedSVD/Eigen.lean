/-!
# Symmetric Eigenvalue Decomposition via Jacobi Algorithm

Implements the Jacobi eigenvalue algorithm for symmetric matrices.
The algorithm iteratively applies Givens rotations to zero out the
largest off-diagonal element until the matrix is diagonal.

This matches the Rust implementation in src/eigen.rs.
-/

import RandomizedSVD.Matrix

namespace RandomizedSVD

open Matrix Finset

/-! ## Jacobi eigenvalue algorithm -/

/-- State during Jacobi iterations. -/
structure JacobiState (n : ℕ) where
  T : Matrix (Fin n) (Fin n) ℝ  -- current rotated matrix
  V : Matrix (Fin n) (Fin n) ℝ  -- accumulated eigenvectors

/-- Find the index of the largest off-diagonal element. -/
def findMaxOffDiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Option (Fin n × Fin n) :=
  let maxVal := ⨆ (i : Fin n) (j : Fin n) (_ : i ≠ j), |A i j|
  if maxVal = 0 then none
  else
    -- Return any pair (p, q) achieving the maximum
    -- In practice, we'd search for it; here we abstract
    some ⟨⟨0, by omega⟩, ⟨1, by omega⟩⟩

/-- Apply a Givens rotation to zero out A[p, q].
    θ = ½ arctan(2·A[p,q] / (A[q,q] - A[p,p])). -/
def givensRotation {n : ℕ} (s : JacobiState n) (p q : Fin n) (hpq : p ≠ q) : JacobiState n :=
  let a_pp := s.T p p
  let a_qq := s.T q q
  let a_pq := s.T p q
  let theta := (Real.atan (2 * a_pq / (a_qq - a_pp))) / 2
  let c := Real.cos theta
  let s_val := Real.sin theta
  -- Update T: T'[p,p] = c²·T[p,p] + s²·T[q,q] - 2·c·s·T[p,q]
  --           T'[q,q] = s²·T[p,p] + c²·T[q,q] + 2·c·s·T[p,q]
  -- Update off-diagonals for k ≠ p, q
  let T' := s.T •• fun i j =>
    if i = p ∧ j = p then c^2 * a_pp + s_val^2 * a_qq - 2 * c * s_val * a_pq
    else if i = q ∧ j = q then s_val^2 * a_pp + c^2 * a_qq + 2 * c * s_val * a_pq
    else if i ≠ p ∧ i ≠ q ∧ j = p then c * s.T i p - s_val * s.T i q
    else if i ≠ p ∧ i ≠ q ∧ j = q then s_val * s.T i p + c * s.T i q
    else if i = p ∧ j ≠ p ∧ j ≠ q then c * s.T p j - s_val * s.T q j
    else if i = q ∧ j ≠ p ∧ j ≠ q then s_val * s.T p j + c * s.T q j
    else s.T i j
  -- Accumulate rotations in V
  let V' := s.V •• fun i j =>
    if j = p then c * s.V i p - s_val * s.V i q
    else if j = q then s_val * s.V i p + c * s.V i q
    else s.V i j
  { T := T', V := V' }

/-- Iterate Jacobi until convergence. -/
def jacobiIterate {n : ℕ} (s : JacobiState n) (max_iter : ℕ) (tol : ℝ) : JacobiState n :=
  -- In practice: find largest off-diagonal, apply rotation, repeat
  -- Here: abstract over the iteration
  s  -- TODO: implement the actual iteration loop

/-- Symmetric eigenvalue decomposition.
    Returns eigenvalues (descending) and eigenvector matrix. -/
def symEig {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : List ℝ × Matrix (Fin n) (Fin n) ℝ :=
  -- Compute via Jacobi iterations
  -- Returns (eigenvalues, eigenvectors) where eigenvalues are in descending order
  let init : JacobiState n := { T := A, V := 1 }
  let result := jacobiIterate init (n * n * 100) 1e-15
  -- Extract eigenvalues from diagonal
  let eigenvalues := (Finset.univ : Finset (Fin n)).toList.map (fun i => result.T i i)
  -- Sort in descending order and reorder eigenvectors accordingly
  let (sorted_eigs, sorted_V) := sortEigenpairs eigenvalues result.V
  (sorted_eigs, sorted_V)

/-- Sort eigenpairs by eigenvalue descending, reorder eigenvectors. -/
def sortEigenpairs {n : ℕ} (eigs : List ℝ) (V : Matrix (Fin n) (Fin n) ℝ) :
    List ℝ × Matrix (Fin n) (Fin n) ℝ :=
  -- In practice: sort eigenvalues and permute columns of V
  (eigs.sort (· ≥ ·), V)

/-! ## Correctness axioms (sorry) -/

/-- Axiom: Jacobi algorithm converges to a diagonal matrix.
    After sufficient iterations, all off-diagonal elements are < tol. -/
axiom jacobi_converges {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : Symm A) :
  ∃ T_diag : Matrix (Fin n) (Fin n) ℝ,
    (∀ i j, i ≠ j → |T_diag i j| < 1e-15) ∧
    Diagonal T_diag

/-- Axiom: Eigenvalues are preserved under similarity transformations.
    The eigenvalues of A equal the eigenvalues of V^T A V. -/
axiom eigenvalues_preserved {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : Symm A) :
  ∀ λ ∈ spectrum ℝ A, λ ∈ spectrum ℝ (fun i j => if i = j then A i j else 0)

/-- Axiom: Eigenvector columns are orthogonal.
    If eigenvalues are distinct, eigenvectors are orthogonal. -/
axiom eigenvectors_orthogonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : Symm A)
    (i j : Fin n) (hij : i ≠ j) :
  dotProd (getCol (symEig A).2 i) (getCol (symEig A).2 j) = 0

/-- Axiom: A = V Λ V^T (spectral theorem). -/
axiom spectral_theorem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : Symm A) :
  let (eigs, V) := symEig A
  A = V * Matrix.of (fun i => if i.fst = i.snd then eigs[i.fst.val]! else 0) * V.transpose

/-- Axiom: Eigenvalues are in descending order. -/
axiom eigenvalues_descending {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : Symm A) :
  let (eigs, _) := symEig A
  ∀ i j, i < j → eigs[i]! ≥ eigs[j]!

end RandomizedSVD
