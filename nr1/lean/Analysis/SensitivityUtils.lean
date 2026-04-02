import LUDecomp.FloatLU
import LUDecomp.FloatMatrix
import LUDecomp.ConditionNumber
import Fuzz.RandomGen

/-!
# Sensitivity Analysis Utilities
-/

namespace Analysis

open LUDecomp.FloatMat LUDecomp.FloatLU LUDecomp.ConditionNumber Fuzz

def diagSigma (n : Nat) (targetKappa : Float) : FMat :=
  fromFn n n fun i j =>
    if i == j then
      if i == 0 then targetKappa
      else if i == n - 1 then 1.0
      else
        let t := Float.ofNat i / Float.ofNat (n - 1)
        targetKappa * (1.0 / targetKappa).pow t
    else 0.0

def randOrthogonalApprox (state : PrngState) (n : Nat) : FMat × PrngState := Id.run do
  let (Q, state') := randMatrix state n (-1.0) 1.0
  let mut Q' := Q
  for j in [:n] do
    let mut norm := 0.0
    for i in [:n] do
      let v := get Q' i j
      norm := norm + v * v
    norm := norm.sqrt
    if norm > 1e-15 then
      for i in [:n] do
        Q' := set Q' i j (get Q' i j / norm)
    for k in [j + 1 : n] do
      let mut dot := 0.0
      for i in [:n] do
        dot := dot + get Q' i j * get Q' i k
      for i in [:n] do
        Q' := set Q' i k (get Q' i k - dot * get Q' i j)
  return (Q', state')

def generateConditionedMatrix (state : PrngState) (n : Nat) (targetKappa : Float) :
    FMat × PrngState :=
  let (Q, state') := randOrthogonalApprox state n
  let S := diagSigma n targetKappa
  let QS := mulMat Q S
  let QT := fromFn n n fun i j => get Q j i
  let A := mulMat QS QT
  (A, state')

def forwardError (xComp xTrue : FVec) : Float :=
  let diff := vecSub xComp xTrue
  let errNorm := vecNormInf diff
  let trueNorm := vecNormInf xTrue
  if trueNorm > 0.0 then errNorm / trueNorm else errNorm

def backwardError (A : FMat) (x b : FVec) : Float :=
  let Ax := mulVec A x
  let residual := vecSub Ax b
  let resNorm := vecNormInf residual
  let denom := normInf A * vecNormInf x + vecNormInf b
  if denom > 0.0 then resNorm / denom else resNorm

structure TrialResult where
  actualKappa : Float
  forwardErr : Float
  backwardErr : Float

def runTrial (state : PrngState) (n : Nat) (targetKappa : Float) :
    TrialResult × PrngState := Id.run do
  let (A, state') := generateConditionedMatrix state n targetKappa
  let mut s := state'
  let mut xTrue : Array Float := #[]
  for _ in [:n] do
    let (v, s') := nextFloatRange s (-1.0) 1.0
    xTrue := xTrue.push v
    s := s'
  let b := mulVec A xTrue
  match solve A b with
  | none =>
    return ({ actualKappa := (1.0/0.0 : Float), forwardErr := (1.0/0.0 : Float), backwardErr := (1.0/0.0 : Float) }, s)
  | some xComp =>
    let kappa := conditionNumber1 A
    let fErr := forwardError xComp xTrue
    let bErr := backwardError A xComp b
    return ({ actualKappa := kappa, forwardErr := fErr, backwardErr := bErr }, s)

end Analysis
