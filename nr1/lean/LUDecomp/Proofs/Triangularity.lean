import LUDecomp.LU

/-!
# Triangularity Proofs

Proves that the L returned by `luDecompose` is unit lower triangular
and that U is upper triangular.

Note: These proofs work over exact arithmetic (ℚ).
Floating-point versions cannot be formally verified.
-/

namespace LUDecomp.Proofs

/-- L is lower triangular: entries above the diagonal are zero.
    For all i < j, L i j = 0. -/
theorem L_lower_triangular {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ) :
    let lu := luDecompose A
    ∀ i j : Fin n, i < j → lu.L i j = 0 := by
  sorry  -- TODO: prove by induction on luStep

/-- L has unit diagonal: L i i = 1 for all i. -/
theorem L_unit_diagonal {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ) :
    let lu := luDecompose A
    ∀ i : Fin n, lu.L i i = 1 := by
  sorry  -- TODO: follows from luDecompose definition (diagonal set to 1)

/-- U is upper triangular: entries below the diagonal are zero.
    For all i > j, U i j = 0. -/
theorem U_upper_triangular {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ) :
    let lu := luDecompose A
    ¬lu.singular → ∀ i j : Fin n, i > j → lu.U i j = 0 := by
  sorry  -- TODO: prove by induction on elimination steps

end LUDecomp.Proofs
