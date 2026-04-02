import LUDecomp.FloatMatrix

/-!
# Float LU Decomposition

IEEE 754 double-precision implementation of LU decomposition with partial pivoting.
Uses `Array (Array Float)` for efficient computation.
-/

namespace LUDecomp.FloatLU

open FloatMat

/-- Result of floating-point LU decomposition. -/
structure FloatLUResult where
  /-- Unit lower triangular matrix -/
  L : FMat
  /-- Upper triangular matrix -/
  U : FMat
  /-- Permutation as array: perm[i] = original row index -/
  perm : Array Nat
  /-- Number of row swaps (for determinant sign) -/
  numSwaps : Nat
  /-- Whether a zero pivot was encountered -/
  singular : Bool

/-- Find the row with the largest absolute value in column `col`,
    starting from row `startRow`. -/
def findPivotRow (U : FMat) (col startRow : Nat) : Nat := Id.run do
  let n := nrows U
  let mut best := startRow
  let mut bestVal := (get U startRow col).abs
  for i in [startRow + 1 : n] do
    let v := (get U i col).abs
    if v > bestVal then
      best := i
      bestVal := v
  return best

/-- LU decomposition with partial pivoting. -/
def decompose (A : FMat) : FloatLUResult := Id.run do
  let n := nrows A
  let mut U := A
  let mut L := identity n
  let mut perm := Array.ofFn (n := n) fun i => i.val
  let mut numSwaps := 0
  let mut singular := false
  for k in [:n] do
    if singular then
      break
    let pivotRow := findPivotRow U k k
    if pivotRow != k then
      U := swapRows U k pivotRow
      let tmp := perm[k]!
      perm := perm.set! k perm[pivotRow]!
      perm := perm.set! pivotRow tmp
      numSwaps := numSwaps + 1
      for j in [:k] do
        let tmp := get L k j
        L := set L k j (get L pivotRow j)
        L := set L pivotRow j tmp
    let pivotVal := get U k k
    if pivotVal.abs < 1e-300 then
      singular := true
      break
    for i in [k + 1 : n] do
      let factor := get U i k / pivotVal
      L := set L i k factor
      for j in [k : n] do
        let newVal := get U i j - factor * get U k j
        U := set U i j newVal
  return { L, U, perm, numSwaps, singular }

/-- Forward substitution: solve Ly = b where L is unit lower triangular. -/
def forwardSub (L : FMat) (b : FVec) : FVec := Id.run do
  let n := b.size
  let mut y := Array.replicate n 0.0
  for i in [:n] do
    let mut sum := 0.0
    for j in [:i] do
      sum := sum + get L i j * y[j]!
    y := y.set! i (b[i]! - sum)
  return y

/-- Back substitution: solve Ux = y where U is upper triangular. -/
def backSub (U : FMat) (y : FVec) : Option FVec := Id.run do
  let n := y.size
  let mut x := Array.replicate n 0.0
  for ki in [:n] do
    let i := n - 1 - ki
    let mut sum := 0.0
    for j in [i + 1 : n] do
      sum := sum + get U i j * x[j]!
    let diag := get U i i
    if diag.abs < 1e-300 then
      return none
    x := x.set! i ((y[i]! - sum) / diag)
  return some x

/-- Apply the permutation to a vector: result[i] = b[perm[i]]. -/
def applyPerm (perm : Array Nat) (b : FVec) : FVec :=
  perm.map fun i => b[i]!

/-- Solve Ax = b using LU decomposition. -/
def solve (A : FMat) (b : FVec) : Option FVec :=
  let lu := decompose A
  if lu.singular then none
  else
    let pb := applyPerm lu.perm b
    let y := forwardSub lu.L pb
    backSub lu.U y

/-- Compute determinant from LU decomposition. -/
def determinant (A : FMat) : Float := Id.run do
  let lu := decompose A
  if lu.singular then return 0.0
  let n := nrows lu.U
  let mut det := if lu.numSwaps % 2 == 0 then 1.0 else -1.0
  for i in [:n] do
    det := det * get lu.U i i
  return det

end LUDecomp.FloatLU
