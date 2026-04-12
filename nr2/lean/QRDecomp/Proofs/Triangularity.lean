import QRDecomp.QR

/-!
# Triangularity Proofs

R upper-triangularity is proved from the explicit construction in `qrDecompose`.
R unit diagonal is proved from the explicit `if i = j then 1` construction.
-/

namespace QRDecomp.Proofs

/-- R is upper triangular: entries below the diagonal are zero.
    Proved: follows from the explicit construction
    `if i.val > j.val then 0 else ...` in `qrDecompose`. -/
theorem R_upper_triangular {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) (hij : i > j) :
    (qrDecompose A).R i j = 0 := by
  show (if i.val > j.val then (0 : ℚ) else if i = j then 1 else _) = 0
  simp [Fin.val_fin_lt.mp hij]

/-- R has unit diagonal: R i i = 1 for all i (unnormalized convention).
    Proved: follows from the explicit construction
    `if i = j then 1 else ...` in `qrDecompose`. -/
theorem R_unit_diagonal {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) :
    (qrDecompose A).R i i = 1 := by
  show (if i.val > i.val then (0 : ℚ) else if i = i then 1 else _) = 1
  simp

end QRDecomp.Proofs
