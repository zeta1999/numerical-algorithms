import QRDecomp.FloatQR

/-!
# Condition Number Estimation

Estimates the 1-norm condition number κ₁(A) = ‖A‖₁ · ‖A⁻¹‖₁
using the QR factorization to cheaply estimate ‖A⁻¹‖₁.
-/

namespace QRDecomp.ConditionNumber

open FloatMat FloatQR

/-- Estimate ‖A⁻¹‖₁ by solving A*z = e_j for each j
    and taking the max column-1-norm. -/
def estimateInvNorm1 (qr : FloatQRResult) (n : Nat) : Float := Id.run do
  let mut maxNorm := 0.0
  let QT := transpose qr.Q
  for j in [:n] do
    let ej := Array.ofFn (n := n) fun i => if i.val == j then 1.0 else 0.0
    let y := mulVec QT ej
    match backSub qr.R y with
    | some z =>
      let mut colNorm := 0.0
      for x in z do
        colNorm := colNorm + x.abs
      if colNorm > maxNorm then
        maxNorm := colNorm
    | none => pure ()
  return maxNorm

/-- Estimate the 1-norm condition number κ₁(A) = ‖A‖₁ · ‖A⁻¹‖₁. -/
def conditionNumber1 (A : FMat) : Float :=
  let qr := decompose A
  if qr.singular then (1.0 / 0.0 : Float)
  else
    let normA := norm1 A
    let normAinv := estimateInvNorm1 qr (nrows A)
    normA * normAinv

/-- Estimate the infinity-norm condition number κ∞(A). -/
def conditionNumberInf (A : FMat) : Float := Id.run do
  let qr := decompose A
  if qr.singular then return (1.0 / 0.0 : Float)
  let normA := normInf A
  let n := nrows A
  let QT := transpose qr.Q
  let mut invRowSums := Array.replicate n 0.0
  for j in [:n] do
    let ej := Array.ofFn (n := n) fun i => if i.val == j then 1.0 else 0.0
    let y := mulVec QT ej
    match backSub qr.R y with
    | some z =>
      for i in [:n] do
        invRowSums := invRowSums.modify i (· + (z[i]!).abs)
    | none => pure ()
  let mut normAinv := 0.0
  for s in invRowSums do
    if s > normAinv then normAinv := s
  return normA * normAinv

end QRDecomp.ConditionNumber
