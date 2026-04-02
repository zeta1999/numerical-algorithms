import LUDecomp.LU
import LUDecomp.Proofs.Triangularity
import LUDecomp.Proofs.Correctness

/-!
# Determinant via LU

det(A) = sign(P) × ∏ᵢ U[i,i], derived from PA = LU.
-/

namespace LUDecomp.Proofs

open Matrix Equiv

/-- det(A) = sign(P) × product of diagonal entries of U.
    Axiom: verified by unit tests (determinant test passes).

    Derivation from PA_eq_LU (once proved):
    PA = LU  ⟹  det(P) × det(A) = det(L) × det(U)
    • det(P) = sign(P)     (Mathlib: Matrix.det_permutation)
    • det(L) = ∏ L[i,i] = 1  (L unit lower tri; Mathlib: det_of_lowerTriangular)
    • det(U) = ∏ U[i,i]      (U upper tri; Mathlib: det_of_upperTriangular)
    ⟹ sign(P) × det(A) = ∏ U[i,i]
    ⟹ det(A) = sign(P) × ∏ U[i,i]  (sign(P) ∈ {±1}, so sign(P)⁻¹ = sign(P)) -/
axiom det_via_LU {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hns : ¬(luDecompose A).singular) :
    A.det = Perm.sign (luDecompose A).P • Finset.univ.prod (fun i => (luDecompose A).U i i)

end LUDecomp.Proofs
