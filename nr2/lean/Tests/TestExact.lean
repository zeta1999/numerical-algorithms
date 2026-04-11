import QRDecomp.QR
import QRDecomp.Solve

/-!
# Exact arithmetic unit tests
-/

namespace Tests.Exact

open QRDecomp

/-- Helper: create a 2×2 rational matrix from values. -/
def mat2x2 (a b c d : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![a, b; c, d]

/-- Helper: create a 3×3 rational matrix. -/
def mat3x3 (a b c d e f g h i : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![a, b, c; d, e, f; g, h, i]

def test_identity_2x2 : Bool :=
  let A := mat2x2 1 0 0 1
  let qr := qrDecompose A
  !qr.singular

def test_simple_2x2 : Bool :=
  let A := mat2x2 2 1 4 3
  let qr := qrDecompose A
  !qr.singular

def test_solve_2x2 : Bool :=
  let A := mat2x2 2 1 4 3
  let b : Fin 2 → ℚ := ![5, 11]
  match solveQR A b with
  | some x => decide (x 0 = 2 ∧ x 1 = 1)
  | none => false

def test_solve_3x3 : Bool :=
  let A := mat3x3 1 2 3 4 5 6 7 8 10
  let b : Fin 3 → ℚ := ![6, 15, 25]
  match solveQR A b with
  | some x =>
    (x 0 == 1) && (x 1 == 1) && (x 2 == 1)
  | none => false

def test_singular : Bool :=
  let A := mat2x2 1 2 2 4
  let b : Fin 2 → ℚ := ![3, 6]
  match solveQR A b with
  | some _ => false
  | none => true

def runAll : Nat × Nat :=
  let tests := [
    ("identity_2x2", test_identity_2x2),
    ("simple_2x2", test_simple_2x2),
    ("solve_2x2", test_solve_2x2),
    ("solve_3x3", test_solve_3x3),
    ("singular", test_singular)
  ]
  let passed := tests.filter (·.2) |>.length
  (passed, tests.length)

end Tests.Exact
