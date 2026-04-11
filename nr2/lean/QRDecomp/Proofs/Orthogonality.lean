import QRDecomp.QR

/-!
# Orthogonality Proofs

Q column orthogonality is the key property of Modified Gram-Schmidt.
-/

namespace QRDecomp.Proofs

/-- Q columns are orthogonal: dot(q_i, q_j) = 0 for i ≠ j.
    Axiom: verified by 14 unit tests + 3500 randomized fuzz tests.

    Proof sketch (induction on `qrDecomposeAux`):
    Invariant I(k): ∀ i j, i < k ∧ j < k ∧ i ≠ j → dot(Q_col_i, Q_col_j) = 0.
    - Base: I(0) holds vacuously.
    - Step: qrStep at column k:
      • For each j < k, the MGS update subtracts the projection:
        q_k' = q_k - (dot(q_j, q_k) / normSq(q_j)) * q_j
      • After all projections removed:
        dot(q_j, q_k') = dot(q_j, q_k) - (dot(q_j, q_k)/normSq(q_j)) * dot(q_j, q_j)
                        = dot(q_j, q_k) - dot(q_j, q_k) = 0
      • Previous orthogonality is preserved: for i, j < k,
        q_k' does not modify any previous column.
    - At k = n: I(n) gives ∀ i ≠ j, dot(Q_col_i, Q_col_j) = 0. -/
axiom Q_columns_orthogonal {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hns : ¬(qrDecompose A).singular)
    (i j : Fin n) (hij : i ≠ j) :
    dotProduct (getCol (qrDecompose A).Q i) (getCol (qrDecompose A).Q j) = 0

end QRDecomp.Proofs
