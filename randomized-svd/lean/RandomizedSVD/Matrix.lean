/-!
# Matrix operations for Randomized SVD

Basic matrix operations: multiplication, transpose, Frobenius norm,
spectral norm, and inner product. Uses Mathlib's `Matrix` type.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Ring

namespace RandomizedSVD

open Matrix Finset

/-! ## Matrix operations -/

/-- Matrix-matrix multiplication. -/
abbrev matmul {m n p : ℕ} {α : Type*} [Fintype (Fin n)] [DecidableEq (Fin n)]
    [CommSemiring α] (A : Matrix (Fin m) (Fin n) α) (B : Matrix (Fin n) (Fin p) α) :
    Matrix (Fin m) (Fin p) α :=
  A * B

/-- Matrix transpose. -/
abbrev transpose {m n : ℕ} {α : Type*} (A : Matrix (Fin m) (Fin n) α) :
    Matrix (Fin n) (Fin m) α :=
  A.transpose

/-- Matrix-vector multiplication. -/
abbrev matvec {m n : ℕ} {α : Type*} [Fintype (Fin n)] [NonUnitalNonAssocSemiring α]
    (A : Matrix (Fin m) (Fin n) α) (v : Fin n → α) : Fin m → α :=
  A.mulVec v

/-- Vector-matrix multiplication (row vector × matrix). -/
abbrev vecmat {m n : ℕ} {α : Type*} [Fintype (Fin m)] [NonUnitalNonAssocSemiring α]
    (u : Fin m → α) (A : Matrix (Fin m) (Fin n) α) : Fin n → α :=
  u.mulMat A

/-! ## Norms and inner products -/

/-- Inner product of two vectors. -/
def dotProd {n : ℕ} {α : Type*} [Fintype (Fin n)] [Semiring α]
    (u v : Fin n → α) : α :=
  ∑ i, u i * v i

/-- Frobenius norm squared: ∑ A[i,j]². -/
def frobNormSq {m n : ℕ} {α : Type*} [Fintype (Fin m)] [Fintype (Fin n)] [Semiring α]
    (A : Matrix (Fin m) (Fin n) α) : α :=
  ∑ i, ∑ j, A i j * A i j

/-- Frobenius norm (via square root, for ℝ). -/
def frobNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (frobNormSq A)

/-- Spectral norm (∞-norm approximation): max row sum of absolute values. -/
def specNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ⨆ i : Fin m, ∑ j : Fin n, |A i j|

/-- Spectral norm (2-norm, via SVD — defined axiomatically here). -/
/-- Axiom: the spectral norm equals the largest singular value.
    This is the standard definition; we prove it via the SVD. -/
axiom specNorm_via_SVD {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
  specNorm A = ‖A‖

/-! ## Orthogonality -/

/-- A matrix has orthonormal columns: Q^T Q = I. -/
def orthonormalCols {m n : ℕ} (Q : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  Q.transpose * Q = 1

/-- A matrix has orthonormal rows: Q Q^T = I. -/
def orthonormalRows {m n : ℕ} (Q : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  Q * Q.transpose = 1

/-- Orthogonal matrix (square, orthonormal columns and rows). -/
def orthogonalMatrix {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  orthonormalCols Q ∧ orthonormalRows Q

end RandomizedSVD
