import LUDecomp.LU
import LUDecomp.Proofs.Triangularity
import LUDecomp.Proofs.Correctness
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Determinant via LU

Proves that det(A) = sign(P) × ∏ᵢ U[i,i].

The proof chain:
  PA = LU                          (PA_eq_LU)
  det(PA) = det(LU)
  det(P) * det(A) = det(L) * det(U)   (det_mul)
  sign(P) * det(A) = 1 * ∏ᵢ U[i,i]   (det of perm, det of triangular)
  det(A) = sign(P) * ∏ᵢ U[i,i]       (sign(P)² = 1)
-/

namespace LUDecomp.Proofs

open Matrix Equiv

/-- det(A) = sign(P) × product of diagonal entries of U.

TODO: Complete once PA_eq_LU is proved. The proof then follows from:
- `Matrix.det_mul`: det(L * U) = det(L) * det(U)
- L unit lower triangular ⟹ det(L) = ∏ᵢ L[i,i] = ∏ᵢ 1 = 1
  (uses L_unit_diagonal and Mathlib's `Matrix.det_of_lowerTriangular`)
- U upper triangular ⟹ det(U) = ∏ᵢ U[i,i]
  (uses U_upper_triangular and Mathlib's `Matrix.det_of_upperTriangular`)
- det(permMatrix P) = Perm.sign P
  (standard Mathlib result)
- Combining: sign(P) * det(A) = 1 * ∏ᵢ U[i,i]
  so det(A) = sign(P) * ∏ᵢ U[i,i]  (since sign(P)² = 1) -/
theorem det_via_LU {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hns : ¬(luDecompose A).singular) :
    A.det = Perm.sign (luDecompose A).P • Finset.univ.prod (fun i => (luDecompose A).U i i) := by
  sorry

end LUDecomp.Proofs
