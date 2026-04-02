import LUDecomp.LU
import LUDecomp.Solve
import LUDecomp.Permutation

/-!
# Correctness Proofs

The central theorem: PA = LU.
Also: if `solveLU` returns a solution x, then Ax = b (in exact arithmetic).

Note: These proofs work over exact arithmetic (ℚ).
-/

namespace LUDecomp.Proofs

open Matrix

/-- PA = LU: The permuted matrix equals the product of L and U. -/
theorem PA_eq_LU {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ) :
    let lu := luDecompose A
    ¬lu.singular →
    permMatrix lu.P A = lu.L * lu.U := by
  sorry  -- TODO: prove by loop invariant over luStep
  -- Strategy: define the invariant at step k that
  -- P_k * A = L_k * U_k on the first k columns,
  -- and U_k agrees with the partially eliminated matrix.

/-- Solution correctness: if solveLU returns x, then A * x = b. -/
theorem solve_correct {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ)
    (b : Fin n → ℚ)
    (x : Fin n → ℚ) :
    solveLU A b = some x →
    A.mulVec x = b := by
  sorry  -- TODO: follows from PA_eq_LU + forwardSub/backSub correctness
  -- Key steps:
  -- 1. solveLU returns x means backSub returned x and lu was not singular
  -- 2. backSub U x = some x implies U * x = y
  -- 3. forwardSub L (P*b) = y implies L * y = P * b
  -- 4. Therefore A * x = P⁻¹ * L * U * x = P⁻¹ * L * y = P⁻¹ * P * b = b

end LUDecomp.Proofs
