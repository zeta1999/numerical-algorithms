import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Sign

/-!
# Permutation utilities for LU decomposition

Represents row permutations as `Equiv.Perm (Fin n)` and provides
conversion to/from permutation matrices.
-/

namespace LUDecomp

open Equiv Matrix

/-- Convert a permutation to a permutation matrix. -/
def permToMatrix {n : ℕ} [DecidableEq (Fin n)]
    (σ : Perm (Fin n)) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if σ i = j then 1 else 0

/-- Apply a permutation to a vector. -/
def applyPerm {n : ℕ} {α : Type*} (σ : Perm (Fin n)) (v : Fin n → α) : Fin n → α :=
  v ∘ σ

/-- Compose two permutations: apply σ₂ first, then σ₁. -/
def composePerm {n : ℕ} (σ₁ σ₂ : Perm (Fin n)) : Perm (Fin n) :=
  σ₁ * σ₂

/-- The elementary permutation that swaps rows `i` and `j`. -/
def swapPerm {n : ℕ} (i j : Fin n) : Perm (Fin n) :=
  Equiv.swap i j

/-- Apply a permutation to a matrix (permute rows). -/
def permMatrix {n m : ℕ} {α : Type*} (σ : Perm (Fin n))
    (A : Matrix (Fin n) (Fin m) α) : Matrix (Fin n) (Fin m) α :=
  fun i c => A (σ i) c

end LUDecomp
