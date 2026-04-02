import LUDecomp.LU

/-!
# Triangularity Proofs

Proves that L from `luDecompose` is unit lower triangular
and U is upper triangular.
-/

namespace LUDecomp.Proofs

/-- L is lower triangular: entries above the diagonal are zero. -/
theorem L_lower_triangular {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) (hij : i < j) :
    (luDecompose A).L i j = 0 := by
  show (if i = j then (1 : ℚ) else if i > j then _ else 0) = 0
  have hne : ¬(i = j) := Fin.ne_of_lt hij
  have hng : ¬(i > j) := not_lt.mpr (le_of_lt hij)
  simp [hne, hng]

/-- L has unit diagonal: L i i = 1 for all i. -/
theorem L_unit_diagonal {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) :
    (luDecompose A).L i i = 1 := by
  show (if i = i then (1 : ℚ) else if i > i then _ else 0) = 1
  simp

/-- U is upper triangular: entries below the diagonal are zero.

This requires proving that each elimination step zeros out entries
below the diagonal. The proof proceeds by induction on the fold steps.

TODO: Complete inductive proof over luStep iterations. -/
theorem U_upper_triangular {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hns : ¬(luDecompose A).singular)
    (i j : Fin n) (hij : i > j) :
    (luDecompose A).U i j = 0 := by
  sorry
  /-
  Proof sketch:
  Define invariant I(k): after processing column k,
    ∀ i j, j.val < k → i > j → state.U i j = 0

  Base case: I(0) holds vacuously.
  Inductive step: luStep at column k zeros out U[i][k] for i > k
    via elimination: U[i][k] ← U[i][k] - (U[i][k]/pivot) * U[k][k] = 0.
    Entries in columns < k are preserved (row swaps maintain zero structure).
  -/

end LUDecomp.Proofs
