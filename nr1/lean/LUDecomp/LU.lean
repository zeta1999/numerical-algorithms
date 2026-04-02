import LUDecomp.Matrix
import LUDecomp.Permutation
import Mathlib.Data.Rat.Defs

/-!
# LU Decomposition (Doolittle with partial pivoting)

Implements PA = LU decomposition over ℚ.
Uses Doolittle's method: L is unit lower triangular, U is upper triangular.
Partial pivoting selects the largest absolute value in the current column.
-/

namespace LUDecomp

open Equiv

/-- Result of LU decomposition. -/
structure LUResult (n : ℕ) (α : Type*) where
  /-- Unit lower triangular matrix -/
  L : Matrix (Fin n) (Fin n) α
  /-- Upper triangular matrix -/
  U : Matrix (Fin n) (Fin n) α
  /-- Row permutation -/
  P : Perm (Fin n)
  /-- Whether the matrix is singular -/
  singular : Bool

/-- Absolute value for ℚ (numerator absolute value / denominator). -/
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
  -- Find pivot
  let pivotRow := findPivot s.U k k
  -- Swap rows in U
  let U' := swapRows s.U k pivotRow
  -- Swap rows in L (only the part already computed, columns < k)
  let L' := fun i j =>
    if j < k then
      if i = k then s.L pivotRow j
      else if i = pivotRow then s.L k j
      else s.L i j
    else s.L i j
  -- Update permutation
  let P' := composePerm s.P (swapPerm k pivotRow)
  -- Check for zero pivot
  let pivotVal := U' k k
  if pivotVal == 0 then
    { L := L', U := U', P := P', singular := true }
  else
    -- Eliminate below diagonal
    let L'' := fun i j =>
      if i > k ∧ j = k then U' i k / pivotVal
      else L' i j
    let U'' := fun i j =>
      if i > k then
        U' i j - (U' i k / pivotVal) * U' k j
      else U' i j
    { L := L'', U := U'', P := P', singular := false }

/-- LU decomposition with partial pivoting.
    Decomposes A into PA = LU where:
    - L is unit lower triangular
    - U is upper triangular
    - P is a permutation -/
def luDecompose {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℚ) : LUResult n ℚ :=
  let init : LUState n :=
    { L := (1 : Matrix (Fin n) (Fin n) ℚ)
      U := A
      P := Equiv.refl (Fin n)
      singular := false }
  let result := (List.finRange n).foldl
    (fun (state : LUState n) k =>
      if state.singular then state
      else luStep state k)
    init
  -- Set diagonal of L to 1
  let L := fun i j =>
    if i = j then 1
    else if i > j then result.L i j
    else 0
  { L := L
    U := result.U
    P := result.P
    singular := result.singular }

end LUDecomp
