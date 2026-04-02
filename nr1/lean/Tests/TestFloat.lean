import LUDecomp.FloatLU
import LUDecomp.FloatMatrix
import LUDecomp.ConditionNumber

/-!
# Floating-point unit tests
-/

namespace Tests.FloatTests

open LUDecomp.FloatMat LUDecomp.FloatLU

def eps : Float := 1e-12

def approxZero (x : Float) (tol : Float := eps) : Bool :=
  x.abs < tol

def approxEq (a b : Float) (tol : Float := eps) : Bool :=
  (a - b).abs < tol

def checkReconstruction (A : FMat) (lu : FloatLUResult) (tol : Float := eps) : Bool := Id.run do
  let n := nrows A
  let LU := mulMat lu.L lu.U
  let mut maxDiff := 0.0
  for i in [:n] do
    for j in [:n] do
      let pa_ij := get A (lu.perm[i]!) j
      let lu_ij := get LU i j
      let diff := (pa_ij - lu_ij).abs
      if diff > maxDiff then
        maxDiff := diff
  return maxDiff < tol

def checkLowerTri (L : FMat) : Bool := Id.run do
  let n := nrows L
  let mut ok := true
  for i in [:n] do
    if !approxEq (get L i i) 1.0 then ok := false
    for j in [i + 1 : n] do
      if !approxZero (get L i j) then ok := false
  return ok

def checkUpperTri (U : FMat) : Bool := Id.run do
  let n := nrows U
  let mut ok := true
  for i in [:n] do
    for j in [:i] do
      if !approxZero (get U i j) then ok := false
  return ok

def test_identity : Bool :=
  let A := identity 2
  let lu := decompose A
  !lu.singular && checkReconstruction A lu && checkLowerTri lu.L && checkUpperTri lu.U

def test_2x2 : Bool :=
  let A := fromFn 2 2 fun i j =>
    match i, j with | 0, 0 => 2.0 | 0, 1 => 1.0 | 1, 0 => 4.0 | 1, 1 => 3.0 | _, _ => 0.0
  let lu := decompose A
  !lu.singular && checkReconstruction A lu && checkLowerTri lu.L && checkUpperTri lu.U

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
  let lu := decompose A
  !lu.singular && checkReconstruction A lu 1e-10 && checkLowerTri lu.L && checkUpperTri lu.U

def test_4x4 : Bool :=
  let A := fromFn 4 4 fun i j =>
    match i, j with
    | 0, 0 => 2.0  | 0, 1 => 1.0  | 0, 2 => -1.0 | 0, 3 => 1.0
    | 1, 0 => 4.0  | 1, 1 => 5.0  | 1, 2 => -3.0 | 1, 3 => 5.0
    | 2, 0 => -2.0 | 2, 1 => 5.0  | 2, 2 => -2.0 | 2, 3 => 6.0
    | 3, 0 => 4.0  | 3, 1 => 11.0 | 3, 2 => -4.0 | 3, 3 => 8.0
    | _, _ => 0.0
  let lu := decompose A
  !lu.singular && checkReconstruction A lu && checkLowerTri lu.L && checkUpperTri lu.U

def test_singular : Bool :=
  let A := fromFn 2 2 fun i j =>
    match i, j with | 0, 0 => 1.0 | 0, 1 => 2.0 | 1, 0 => 2.0 | 1, 1 => 4.0 | _, _ => 0.0
  let lu := decompose A
  lu.singular

def test_determinant : Bool :=
  let A := fromFn 2 2 fun i j =>
    match i, j with | 0, 0 => 3.0 | 0, 1 => 7.0 | 1, 0 => 1.0 | 1, 1 => 5.0 | _, _ => 0.0
  approxEq (determinant A) 8.0

def test_cond_identity : Bool :=
  let A := identity 3
  let kappa := LUDecomp.ConditionNumber.conditionNumber1 A
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
