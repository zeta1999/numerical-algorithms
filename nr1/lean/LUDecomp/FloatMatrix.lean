/-!
# Float-based Matrix Operations

Array-backed matrix operations for efficient floating-point computation.
Uses `Array (Array Float)` for O(1) element access.
-/

namespace LUDecomp.FloatMat

/-- A float matrix stored as an array of rows. -/
abbrev FMat := Array (Array Float)

/-- A float vector. -/
abbrev FVec := Array Float

/-- Create an n×m matrix from a function. -/
def fromFn (n m : Nat) (f : Nat → Nat → Float) : FMat :=
  Array.ofFn (n := n) fun i => Array.ofFn (n := m) fun j => f i j

/-- Create an n×n identity matrix. -/
def identity (n : Nat) : FMat :=
  fromFn n n fun i j => if i == j then 1.0 else 0.0

/-- Create an n×m zero matrix. -/
def zeros (n m : Nat) : FMat :=
  fromFn n m fun _ _ => 0.0

/-- Get element at (i, j). -/
def get (A : FMat) (i j : Nat) : Float :=
  (A[i]!)[j]!

/-- Set element at (i, j). -/
def set (A : FMat) (i j : Nat) (v : Float) : FMat :=
  A.modify i (fun row => row.set! j v)

/-- Swap rows i and j. -/
def swapRows (A : FMat) (i j : Nat) : FMat :=
  if i == j then A
  else
    let ri := A[i]!
    let rj := A[j]!
    (A.set! i rj).set! j ri

/-- Number of rows. -/
def nrows (A : FMat) : Nat := A.size

/-- Number of columns. -/
def ncols (A : FMat) : Nat :=
  if A.size > 0 then A[0]!.size else 0

/-- Matrix-vector multiplication. -/
def mulVec (A : FMat) (v : FVec) : FVec := Id.run do
  let mut result : FVec := #[]
  for row in A do
    let mut s := 0.0
    for k in [:row.size] do
      s := s + row[k]! * v[k]!
    result := result.push s
  return result

/-- Matrix-matrix multiplication. -/
def mulMat (A B : FMat) : FMat :=
  let n := nrows A
  let p := ncols B
  fromFn n p fun i j => Id.run do
    let row := A[i]!
    let m := row.size
    let mut s := 0.0
    for k in [:m] do
      s := s + row[k]! * get B k j
    return s

/-- Compute the 1-norm (max column sum of absolute values). -/
def norm1 (A : FMat) : Float := Id.run do
  let n := nrows A
  let m := ncols A
  let mut maxSum := 0.0
  for j in [:m] do
    let mut colSum := 0.0
    for i in [:n] do
      colSum := colSum + (get A i j).abs
    if colSum > maxSum then
      maxSum := colSum
  return maxSum

/-- Compute the infinity-norm (max row sum of absolute values). -/
def normInf (A : FMat) : Float := Id.run do
  let mut mx := 0.0
  for row in A do
    let mut s := 0.0
    for x in row do
      s := s + x.abs
    if s > mx then mx := s
  return mx

/-- Vector infinity-norm. -/
def vecNormInf (v : FVec) : Float := Id.run do
  let mut mx := 0.0
  for x in v do
    if x.abs > mx then mx := x.abs
  return mx

/-- Vector subtraction. -/
def vecSub (a b : FVec) : FVec :=
  Array.ofFn (n := a.size) fun i => a[i]! - b[i]!

end LUDecomp.FloatMat
