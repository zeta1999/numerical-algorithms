import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Matrix utilities for LU decomposition

Convenience wrappers around Mathlib's `Matrix` type for use in
the LU decomposition algorithm.
-/

namespace LUDecomp

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

/-- Subtract a scaled row from another row in-place.
    Sets row `target` to `A[target] - scale * A[source]`. -/
def elimRow {n m : ℕ} {α : Type*} [Ring α]
    (A : Matrix (Fin n) (Fin m) α) (target source : Fin n) (scale : α) :
    Matrix (Fin n) (Fin m) α :=
  fun r c =>
    if r = target then A r c - scale * A source c
    else A r c

end LUDecomp
