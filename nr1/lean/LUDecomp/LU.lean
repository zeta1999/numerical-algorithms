import LUDecomp.Matrix
import LUDecomp.Permutation
import Mathlib.Data.Rat.Defs

/-!
# LU Decomposition (Doolittle with partial pivoting)

Implements PA = LU decomposition over ℚ.
Uses a recursive formulation for both computation and formal verification.
-/

namespace LUDecomp

open Equiv

/-- Result of LU decomposition. -/
structure LUResult (n : ℕ) (α : Type*) where
  L : Matrix (Fin n) (Fin n) α
  U : Matrix (Fin n) (Fin n) α
  P : Perm (Fin n)
  singular : Bool

/-- Absolute value for ℚ. -/
private def ratAbs (q : ℚ) : ℚ :=
  if q < 0 then -q else q

/-- Find the row index with the maximum absolute value in column `col`,
    searching from row `startRow` to `n-1`. -/
def findPivot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (col : Fin n)
    (startRow : Fin n) : Fin n :=
  let rows := List.finRange n |>.filter (· ≥ startRow)
  match rows.argmax (fun i => ratAbs (A i col)) with
  | some idx => idx
  | none => startRow

/-- State during LU decomposition. -/
structure LUState (n : ℕ) where
  L : Matrix (Fin n) (Fin n) ℚ
  U : Matrix (Fin n) (Fin n) ℚ
  P : Perm (Fin n)
  singular : Bool

/-- Perform one step of LU elimination at column `k`. -/
def luStep {n : ℕ} [NeZero n]
    (s : LUState n) (k : Fin n) : LUState n :=
  let pivotRow := findPivot s.U k k
  let U' := swapRows s.U k pivotRow
  let L' := fun i j =>
    if j < k then
      if i = k then s.L pivotRow j
      else if i = pivotRow then s.L k j
      else s.L i j
    else s.L i j
  let P' := composePerm s.P (swapPerm k pivotRow)
  let pivotVal := U' k k
  if pivotVal == 0 then
    { L := L', U := U', P := P', singular := true }
  else
    let L'' := fun i j =>
      if i > k ∧ j = k then U' i k / pivotVal
      else L' i j
    let U'' := fun i j =>
      if i > k then
        U' i j - (U' i k / pivotVal) * U' k j
      else U' i j
    { L := L'', U := U'', P := P', singular := false }

/-- Recursive helper for LU decomposition. Processes columns k..n-1. -/
def luDecomposeAux {n : ℕ} [NeZero n] (s : LUState n) (k : ℕ) (hk : k ≤ n) : LUState n :=
  if heq : k = n then s
  else if s.singular then s
  else
    have hlt : k < n := Nat.lt_of_le_of_ne hk heq
    luDecomposeAux (luStep s ⟨k, hlt⟩) (k + 1) (by omega)
termination_by n - k

/-- LU decomposition with partial pivoting. -/
def luDecompose {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℚ) : LUResult n ℚ :=
  let init : LUState n :=
    { L := (1 : Matrix (Fin n) (Fin n) ℚ)
      U := A
      P := Equiv.refl (Fin n)
      singular := false }
  let result := luDecomposeAux init 0 (Nat.zero_le n)
  let L := fun i j =>
    if i = j then 1
    else if i > j then result.L i j
    else 0
  { L := L
    U := result.U
    P := result.P
    singular := result.singular }

/-! ## Helper lemmas for proofs -/

/-- findPivot returns a row ≥ startRow. -/
theorem findPivot_ge {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (col startRow : Fin n) :
    findPivot A col startRow ≥ startRow := by
  simp only [findPivot]
  split
  · rename_i idx harg
    have hmem : idx ∈ List.filter (· ≥ startRow) (List.finRange n) :=
      List.argmax_mem harg
    exact of_decide_eq_true (List.mem_filter.mp hmem).2
  · exact le_refl _

/-- luDecomposeAux unfold: at k = n, returns state unchanged. -/
@[simp]
theorem luDecomposeAux_eq {n : ℕ} [NeZero n] (s : LUState n) (hk : n ≤ n) :
    luDecomposeAux s n hk = s := by
  unfold luDecomposeAux; simp

/-- luDecomposeAux on singular state returns state unchanged. -/
theorem luDecomposeAux_singular {n : ℕ} [NeZero n] (s : LUState n)
    (k : ℕ) (hk : k ≤ n) (hs : s.singular = true) :
    luDecomposeAux s k hk = s := by
  unfold luDecomposeAux
  split
  · rfl
  · split <;> rfl

/-- The singular flag of luDecomposeAux result. -/
theorem luDecomposeAux_singular_preserved {n : ℕ} [NeZero n] (s : LUState n)
    (k : ℕ) (hk : k ≤ n) (hs : s.singular = true) :
    (luDecomposeAux s k hk).singular = true := by
  rw [luDecomposeAux_singular s k hk hs]
  exact hs

end LUDecomp
