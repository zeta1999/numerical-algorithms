import QRDecomp.FloatQR
import QRDecomp.FloatMatrix
import QRDecomp.ConditionNumber

/-!
# Floating-point unit tests
-/

namespace Tests.FloatTests

open QRDecomp.FloatMat QRDecomp.FloatQR

def eps : Float := 1e-12

def approxZero (x : Float) (tol : Float := eps) : Bool :=
  x.abs < tol

def approxEq (a b : Float) (tol : Float := eps) : Bool :=
  (a - b).abs < tol

/-- Check reconstruction: ||A - QR||_inf < tol -/
def checkReconstruction (A : FMat) (qr : FloatQRResult) (tol : Float := eps) : Bool := Id.run do
  let n := nrows A
  let QR := mulMat qr.Q qr.R
  let mut maxDiff := 0.0
  for i in [:n] do
    for j in [:n] do
      let diff := (get A i j - get QR i j).abs
      if diff > maxDiff then
        maxDiff := diff
  return maxDiff < tol

/-- Check R is upper triangular -/
def checkUpperTri (R : FMat) : Bool := Id.run do
  let n := nrows R
  let mut ok := true
  for i in [:n] do
    for j in [:i] do
      if !approxZero (get R i j) then ok := false
  return ok

/-- Check Q orthogonality: ||Q^T Q - I||_inf < tol -/
def checkOrthogonality (Q : FMat) (tol : Float := eps) : Bool := Id.run do
  let n := nrows Q
  let QTQ := mulMat (transpose Q) Q
  let mut maxDiff := 0.0
  for i in [:n] do
    for j in [:n] do
      let expected := if i == j then 1.0 else 0.0
      let diff := (get QTQ i j - expected).abs
      if diff > maxDiff then
        maxDiff := diff
  return maxDiff < tol

def test_identity : Bool :=
  let A := identity 2
  let qr := decompose A
  !qr.singular && checkReconstruction A qr && checkUpperTri qr.R && checkOrthogonality qr.Q

def test_2x2 : Bool :=
  let A := fromFn 2 2 fun i j =>
    match i, j with | 0, 0 => 2.0 | 0, 1 => 1.0 | 1, 0 => 4.0 | 1, 1 => 3.0 | _, _ => 0.0
  let qr := decompose A
  !qr.singular && checkReconstruction A qr && checkUpperTri qr.R && checkOrthogonality qr.Q

def test_solve_2x2 : Bool :=
  let A := fromFn 2 2 fun i j =>
    match i, j with | 0, 0 => 2.0 | 0, 1 => 1.0 | 1, 0 => 4.0 | 1, 1 => 3.0 | _, _ => 0.0
  let b := #[5.0, 11.0]
  match solve A b with
  | some x => approxEq x[0]! 2.0 && approxEq x[1]! 1.0
  | none => false

def test_3x3 : Bool :=
  let A := fromFn 3 3 fun i j =>
    match i, j with
    | 0, 0 => 1.0 | 0, 1 => 2.0 | 0, 2 => 3.0
    | 1, 0 => 4.0 | 1, 1 => 5.0 | 1, 2 => 6.0
    | 2, 0 => 7.0 | 2, 1 => 8.0 | 2, 2 => 10.0
    | _, _ => 0.0
  let b := #[6.0, 15.0, 25.0]
  match solve A b with
  | some x => approxEq x[0]! 1.0 && approxEq x[1]! 1.0 && approxEq x[2]! 1.0
  | none => false

def test_hilbert_3x3 : Bool :=
  let A := fromFn 3 3 fun i j => 1.0 / Float.ofNat (i + j + 1)
  let qr := decompose A
  !qr.singular && checkReconstruction A qr 1e-10 && checkUpperTri qr.R && checkOrthogonality qr.Q 1e-10

def test_4x4 : Bool :=
  let A := fromFn 4 4 fun i j =>
    match i, j with
    | 0, 0 => 2.0  | 0, 1 => 1.0  | 0, 2 => -1.0 | 0, 3 => 1.0
    | 1, 0 => 4.0  | 1, 1 => 5.0  | 1, 2 => -3.0 | 1, 3 => 5.0
    | 2, 0 => -2.0 | 2, 1 => 5.0  | 2, 2 => -2.0 | 2, 3 => 6.0
    | 3, 0 => 4.0  | 3, 1 => 11.0 | 3, 2 => -4.0 | 3, 3 => 8.0
    | _, _ => 0.0
  let qr := decompose A
  !qr.singular && checkReconstruction A qr && checkUpperTri qr.R && checkOrthogonality qr.Q

def test_singular : Bool :=
  let A := fromFn 2 2 fun i j =>
    match i, j with | 0, 0 => 1.0 | 0, 1 => 2.0 | 1, 0 => 2.0 | 1, 1 => 4.0 | _, _ => 0.0
  let qr := decompose A
  qr.singular

def test_determinant : Bool :=
  let A := fromFn 2 2 fun i j =>
    match i, j with | 0, 0 => 3.0 | 0, 1 => 7.0 | 1, 0 => 1.0 | 1, 1 => 5.0 | _, _ => 0.0
  approxEq (determinant A).abs 8.0

def test_cond_identity : Bool :=
  let A := identity 3
  let kappa := QRDecomp.ConditionNumber.conditionNumber1 A
  approxEq kappa 1.0 1e-10

def runAll : Nat × Nat :=
  let tests := [
    ("identity", test_identity),
    ("2x2", test_2x2),
    ("solve_2x2", test_solve_2x2),
    ("3x3", test_3x3),
    ("hilbert_3x3", test_hilbert_3x3),
    ("4x4", test_4x4),
    ("singular", test_singular),
    ("determinant", test_determinant),
    ("cond_identity", test_cond_identity)
  ]
  let passed := tests.filter (·.2) |>.length
  (passed, tests.length)

end Tests.FloatTests
