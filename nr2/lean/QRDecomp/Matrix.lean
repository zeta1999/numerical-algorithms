import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Matrix utilities for QR decomposition

Convenience wrappers around Mathlib's `Matrix` type for use in
the QR decomposition algorithm.
-/

namespace QRDecomp

open Matrix

/-- Swap two rows of a matrix. -/
def swapRows {n m : ℕ} {α : Type*} (A : Matrix (Fin n) (Fin m) α)
    (i j : Fin n) : Matrix (Fin n) (Fin m) α :=
  A ∘ Equiv.swap i j

/-- Set a single entry of a matrix. -/
def setEntry {n m : ℕ} {α : Type*} [DecidableEq (Fin n)] [DecidableEq (Fin m)]
    (A : Matrix (Fin n) (Fin m) α) (i : Fin n) (j : Fin m) (v : α) :
    Matrix (Fin n) (Fin m) α :=
  fun r c => if r = i ∧ c = j then v else A r c

/-- Extract the diagonal entries of a square matrix as a vector. -/
def diagVec {n : ℕ} {α : Type*} (A : Matrix (Fin n) (Fin n) α) : Fin n → α :=
  fun i => A i i

/-- Build an identity matrix. -/
def identityMatrix {n : ℕ} [DecidableEq (Fin n)] [Zero α] [One α] :
    Matrix (Fin n) (Fin n) α :=
  (1 : Matrix (Fin n) (Fin n) α)

/-- Matrix-vector multiplication. -/
def matVecMul {n m : ℕ} {α : Type*} [Fintype (Fin m)] [NonUnitalNonAssocSemiring α]
    (A : Matrix (Fin n) (Fin m) α) (v : Fin m → α) : Fin n → α :=
  A.mulVec v

/-- Dot product of two vectors. -/
def dotProduct {n : ℕ} {α : Type*} [Fintype (Fin n)] [Mul α] [AddCommMonoid α]
    (u v : Fin n → α) : α :=
  Finset.sum Finset.univ (fun i => u i * v i)

/-- Scalar-vector multiplication. -/
def scaleVec {n : ℕ} {α : Type*} [Mul α] (c : α) (v : Fin n → α) : Fin n → α :=
  fun i => c * v i

/-- Vector subtraction. -/
def subVec {n : ℕ} {α : Type*} [Sub α] (u v : Fin n → α) : Fin n → α :=
  fun i => u i - v i

/-- Extract column j from a matrix. -/
def getCol {n m : ℕ} {α : Type*} (A : Matrix (Fin n) (Fin m) α)
    (j : Fin m) : Fin n → α :=
  fun i => A i j

/-- Set column j of a matrix. -/
def setCol {n m : ℕ} {α : Type*} [DecidableEq (Fin m)]
    (A : Matrix (Fin n) (Fin m) α) (j : Fin m) (v : Fin n → α) :
    Matrix (Fin n) (Fin m) α :=
  fun r c => if c = j then v r else A r c

end QRDecomp
