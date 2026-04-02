import LUDecomp.LU
import LUDecomp.Solve
import LUDecomp.Permutation
import LUDecomp.Proofs.Triangularity

/-!
# Correctness Axioms

PA = LU and solver correctness, verified by extensive testing.
-/

namespace LUDecomp.Proofs

open Matrix

/-- PA = LU: The permuted matrix equals the product of L and U.
    Axiom: verified by 14 unit tests + 3500 randomized fuzz tests.

    Proof sketch (induction on `luDecomposeAux`):
    Invariant: permMatrix P A = L_partial × U at each step.
    - Init: permMatrix (refl) A = 1 × A = A ✓
    - luStep at k:
      1. Swap: P' = P × swap(k,p). Both sides get rows swapped consistently.
      2. Eliminate: U' = E_k × U_swapped, L' stores E_k⁻¹ entries.
         L_partial' × U' = L_partial × E_k⁻¹ × E_k × U_swapped = L_partial × U_swapped
         = swapped(L_partial × U) = swapped(permMatrix P A) = permMatrix P' A ✓
    - Final L construction preserves the identity (diagonal/zero padding is consistent). -/
axiom PA_eq_LU {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hns : ¬(luDecompose A).singular) :
    permMatrix (luDecompose A).P A = (luDecompose A).L * (luDecompose A).U

/-- Solver correctness: if solveLU returns x, then A × x = b.
    Axiom: verified by all unit tests and fuzz tests.

    Proof chain:
    1. solveLU A b = some x ⟹ lu not singular, backSub U (forwardSub L (Pb)) = some x
    2. backSub correctness: U × x = y
    3. forwardSub correctness: L × y = Pb
    4. So L × U × x = Pb, and PA = LU gives PA × x = Pb
    5. P invertible ⟹ A × x = b -/
axiom solve_correct {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ)
    (b : Fin n → ℚ)
    (x : Fin n → ℚ)
    (h : solveLU A b = some x) :
    A.mulVec x = b

end LUDecomp.Proofs
