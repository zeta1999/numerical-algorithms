import QRDecomp.QR

/-!
# Linear System Solver via QR Decomposition

Solves Ax = b by:
1. Decomposing A = QR (Modified Gram-Schmidt)
2. Computing y = Q^T b (using orthogonal Q columns)
3. Solving Rx = y (back substitution)

In the unnormalized convention, Q columns are orthogonal but not unit-length.
y_i = dot(q_i, b) / dot(q_i, q_i), then Rx = y with R having unit diagonal.
-/

namespace QRDecomp

/-- Apply Q^T to vector b using unnormalized Q columns.
    Computes y_i = dot(q_i, b) / normSq(q_i) for each column.
    Uses List.finRange for proper Fin indexing. -/
def applyQTranspose {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    Fin n → ℚ :=
  fun k =>
    let qk := getCol Q k
    let nsq := normSq qk
    if nsq == 0 then 0
    else dotProduct qk b / nsq

/-- Back substitution: solve Rx = y where R is upper triangular.
    Returns `none` if a diagonal entry is zero. -/
def backSubQR {n : ℕ} (R : Matrix (Fin n) (Fin n) ℚ) (y : Fin n → ℚ) :
    Option (Fin n → ℚ) :=
  let result := (List.finRange n).reverse.foldl
    (fun (state : Option (Array ℚ)) (idx : Fin n) =>
      match state with
      | none => none
      | some acc =>
        let sum := (List.finRange n).foldl
          (fun (s : ℚ) (jdx : Fin n) =>
            if jdx.val > idx.val then s + R idx jdx * (acc[jdx.val]!)
            else s)
          0
        let diag := R idx idx
        if diag == 0 then none
        else some (acc.set! idx.val ((y idx - sum) / diag)))
    (some (Array.replicate n 0))
  match result with
  | none => none
  | some arr => some (fun k => arr[k.val]!)

/-- Solve the linear system Ax = b using QR decomposition.
    Returns `none` if A is singular. -/
def solveQR {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℚ)
    (b : Fin n → ℚ) : Option (Fin n → ℚ) :=
  let qr := qrDecompose A
  if qr.singular then none
  else
    let y := applyQTranspose qr.Q b
    backSubQR qr.R y

end QRDecomp
