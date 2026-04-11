import Fuzz.RandomGen
import QRDecomp.FloatQR
import QRDecomp.FloatMatrix

/-!
# Fuzz Testing for QR Decomposition
-/

namespace Fuzz

open QRDecomp.FloatMat QRDecomp.FloatQR

def checkQRProperties (A : FMat) (tol : Float) : Option String := Id.run do
  let n := nrows A
  let qr := decompose A

  if qr.singular then
    return some "unexpectedly singular"

  -- Check R is upper triangular
  for i in [:n] do
    for j in [:i] do
      if !((get qr.R i j).abs < 1e-13) then
        return some s!"R[{i},{j}] = {get qr.R i j}, expected 0"

  -- Check Q orthogonality: ||Q^T Q - I||_inf
  let QTQ := mulMat (transpose qr.Q) qr.Q
  let mut maxOrthErr := 0.0
  for i in [:n] do
    for j in [:n] do
      let expected := if i == j then 1.0 else 0.0
      let diff := (get QTQ i j - expected).abs
      if diff > maxOrthErr then
        maxOrthErr := diff
  if maxOrthErr > tol then
    return some s!"orthogonality error {maxOrthErr} > {tol}"

  -- Check reconstruction: ||A - QR||_inf / ||A||_inf
  let QR := mulMat qr.Q qr.R
  let mut maxDiff := 0.0
  for i in [:n] do
    for j in [:n] do
      let diff := (get A i j - get QR i j).abs
      if diff > maxDiff then
        maxDiff := diff
  let normA := norm1 A
  let relErr := if normA > 0.0 then maxDiff / normA else maxDiff
  if relErr > tol then
    return some s!"reconstruction error {relErr} > {tol}"

  return none

def checkSolve (A : FMat) (state : PrngState) (tol : Float) :
    Option String × PrngState := Id.run do
  let n := nrows A
  let mut s := state
  let mut xTrue : Array Float := #[]
  for _ in [:n] do
    let (v, s') := nextFloatRange s (-10.0) 10.0
    xTrue := xTrue.push v
    s := s'
  let b := mulVec A xTrue
  match solve A b with
  | none => return (some "solve returned none", s)
  | some xComp =>
    let diff := vecSub xComp xTrue
    let errNorm := vecNormInf diff
    let trueNorm := vecNormInf xTrue
    let relErr := if trueNorm > 0.0 then errNorm / trueNorm else errNorm
    if relErr > tol then
      return (some s!"solution error {relErr} > {tol}", s)
    else
      return (none, s)

end Fuzz

open Fuzz QRDecomp.FloatMat QRDecomp.FloatQR in
def main : IO Unit := do
  IO.println "=== QR Decomposition Fuzz Testing ==="
  IO.println ""

  let mut state := initPrng 42
  let mut passed := 0
  let mut failed := 0

  let sizes := #[2, 3, 4, 5, 8, 10, 20]
  let trialsPerSize := 500

  for n in sizes do
    IO.print s!"  n={n}: "
    let mut localFailed := 0
    for _ in [:trialsPerSize] do
      let (A, state') := randDiagDominant state n (-10.0) 10.0
      state := state'
      let tol := Float.ofNat n * 1e-12

      match checkQRProperties A tol with
      | some err =>
        if localFailed < 3 then IO.println s!"    FAIL: {err}"
        localFailed := localFailed + 1
      | none =>
        let (solveResult, state') := checkSolve A state tol
        state := state'
        match solveResult with
        | some err =>
          if localFailed < 3 then IO.println s!"    FAIL: {err}"
          localFailed := localFailed + 1
        | none =>
          passed := passed + 1

    if localFailed > 0 then
      IO.println s!"{trialsPerSize - localFailed}/{trialsPerSize} passed"
      failed := failed + localFailed
    else
      IO.println s!"{trialsPerSize}/{trialsPerSize} passed"

  -- Hilbert matrices
  IO.println ""
  IO.println "  Hilbert matrices (ill-conditioned):"
  for n in #[2, 3, 4, 5, 6, 7, 8] do
    let H := hilbertMatrix n
    let tol := Float.ofNat n * 1e-8
    match checkQRProperties H tol with
    | some err => IO.println s!"    Hilbert {n}x{n}: FAIL - {err}"
    | none => IO.println s!"    Hilbert {n}x{n}: OK"

  IO.println ""
  IO.println s!"=== Results: {passed} passed, {failed} failed ==="
  if failed > 0 then
    IO.Process.exit 1
