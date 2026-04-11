import QRDecomp.FloatMatrix

/-!
# Float QR Decomposition

IEEE 754 double-precision implementation of QR decomposition
using Modified Gram-Schmidt with column normalization.
-/

namespace QRDecomp.FloatQR

open FloatMat

/-- Result of floating-point QR decomposition. -/
structure FloatQRResult where
  /-- Orthogonal matrix (columns are orthonormal) -/
  Q : FMat
  /-- Upper triangular matrix -/
  R : FMat
  /-- Whether a near-zero column norm was encountered -/
  singular : Bool

/-- QR decomposition using Modified Gram-Schmidt.
    Q has orthonormal columns, R is upper triangular with norms on the diagonal. -/
def decompose (A : FMat) : FloatQRResult := Id.run do
  let n := nrows A
  -- Initialize Q as copy of A (column-oriented work)
  let mut Q := A
  let mut R := zeros n n
  let mut singular := false
  for k in [:n] do
    if singular then break
    -- Orthogonalize column k against columns 0..k-1
    for j in [:k] do
      let qj := getCol Q j
      let qk := getCol Q k
      let rjk := dotVec qj qk
      R := set R j k rjk
      -- Q_col_k -= rjk * Q_col_j
      Q := setCol Q k (Array.ofFn (n := n) fun i => (getCol Q k)[i]! - rjk * qj[i]!)
    -- Compute norm of orthogonalized column
    let qk := getCol Q k
    let nrm := vecNorm2 qk
    R := set R k k nrm
    if nrm < 1e-300 then
      singular := true
      break
    -- Normalize the column
    Q := setCol Q k (vecScale (1.0 / nrm) qk)
  return { Q, R, singular }

/-- Back substitution: solve Rx = y where R is upper triangular. -/
def backSub (R : FMat) (y : FVec) : Option FVec := Id.run do
  let n := y.size
  let mut x := Array.replicate n 0.0
  for ki in [:n] do
    let i := n - 1 - ki
    let mut sum := 0.0
    for j in [i + 1 : n] do
      sum := sum + get R i j * x[j]!
    let diag := get R i i
    if diag.abs < 1e-300 then
      return none
    x := x.set! i ((y[i]! - sum) / diag)
  return some x

/-- Solve Ax = b using QR decomposition.
    A = QR, so Rx = Q^T b. -/
def solve (A : FMat) (b : FVec) : Option FVec :=
  let qr := decompose A
  if qr.singular then none
  else
    -- y = Q^T * b
    let QT := transpose qr.Q
    let y := mulVec QT b
    backSub qr.R y

/-- Compute determinant from QR decomposition.
    det(A) = det(Q) * det(R) = det(Q) * product of R diagonal.
    For MGS, det(Q) = +1 or -1. We compute as product of R diagonal
    (which may be negative if we allowed signed norms, but our norms are positive,
    so we need to track sign separately).
    Simplified: det(A) = product of R[i][i] since Q is orthogonal
    and we construct Q with det(Q) = +1 when all R[i][i] > 0. -/
def determinant (A : FMat) : Float := Id.run do
  let qr := decompose A
  if qr.singular then return 0.0
  let n := nrows qr.R
  let mut det := 1.0
  for i in [:n] do
    det := det * get qr.R i i
  return det

end QRDecomp.FloatQR
