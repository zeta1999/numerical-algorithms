import LUDecomp.LU
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Determinant via LU

Proves that det(A) = sign(P) × ∏ᵢ U[i,i].

Since PA = LU:
  det(P) × det(A) = det(L) × det(U)
  det(L) = 1 (unit lower triangular)
  det(U) = ∏ᵢ U[i,i] (upper triangular)
  det(P) = sign(P) = ±1
  Therefore: det(A) = sign(P) × ∏ᵢ U[i,i]
-/

namespace LUDecomp.Proofs

open Matrix Equiv

/-- det(A) = sign(P) × product of diagonal entries of U. -/
theorem det_via_LU {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ) :
    let lu := luDecompose A
    ¬lu.singular →
    A.det = Perm.sign lu.P • Finset.univ.prod (fun i => lu.U i i) := by
  sorry  -- TODO: follows from PA_eq_LU, det_mul, det of triangular matrices
  -- Uses Mathlib:
  -- - Matrix.det_mul
  -- - det of L = 1 (unit lower triangular, product of 1's)
  -- - det of U = product of diagonal (upper triangular)
  -- - det of permutation matrix = sign of permutation

end LUDecomp.Proofs
