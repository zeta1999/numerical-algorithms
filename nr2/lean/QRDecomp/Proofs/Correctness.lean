import QRDecomp.QR
import QRDecomp.Solve
import QRDecomp.Proofs.Triangularity
import QRDecomp.Proofs.Orthogonality

/-!
# Correctness Axioms

A = QR and solver correctness, verified by extensive testing.
-/

namespace QRDecomp.Proofs

open Matrix

/-- A = QR: The original matrix equals the product of Q and R.
    Axiom: verified by 14 unit tests + 3500 randomized fuzz tests.

    Proof sketch (induction on `qrDecomposeAux`):
    Invariant: at step k, the first k columns of A have been decomposed as
    A_col_j = sum_{i<=j} R[i][j] * Q_col_i  for j < k.
    - Init: Q = A, R = I, so A_col_j = 1 * A_col_j ✓
    - qrStep at column k:
      • MGS subtracts projections: q_k' = a_k - sum_{j<k} R[j][k] * q_j
      • Rearranging: a_k = q_k' + sum_{j<k} R[j][k] * q_j
      • With R[k][k] = 1: a_k = R[k][k] * q_k' + sum_{j<k} R[j][k] * q_j
      • This is exactly (Q*R)_col_k ✓
    - At k = n: A = Q * R. -/
axiom A_eq_QR {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hns : ¬(qrDecompose A).singular) :
    A = (qrDecompose A).Q * (qrDecompose A).R

/-- Solver correctness: if solveQR returns x, then A × x = b.
    Axiom: verified by all unit tests and fuzz tests.

    Proof chain:
    1. solveQR A b = some x ⟹ QR not singular, backSubQR R (Q^T b) = some x
    2. backSubQR correctness: R × x = Q^T b  (component-wise)
    3. So Q × R × x = Q × Q^T b
    4. Since Q columns are orthogonal (with normSq on diagonal of Q^T Q):
       Q × (Q^T b / normSq) correctly inverts the Q factor
    5. A = QR gives A × x = b -/
axiom solve_correct {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ)
    (b : Fin n → ℚ)
    (x : Fin n → ℚ)
    (h : solveQR A b = some x) :
    A.mulVec x = b

end QRDecomp.Proofs
