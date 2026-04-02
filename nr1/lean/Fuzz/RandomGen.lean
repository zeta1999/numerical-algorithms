import LUDecomp.FloatMatrix

/-!
# Pseudo-Random Number Generator

Simple xoshiro256** PRNG for reproducible fuzzing.
-/

namespace Fuzz

structure PrngState where
  s0 : UInt64
  s1 : UInt64
  s2 : UInt64
  s3 : UInt64

def rotl (x : UInt64) (k : UInt64) : UInt64 :=
  (x <<< k) ||| (x >>> (64 - k))

def nextUInt64 (state : PrngState) : UInt64 × PrngState :=
  let result := rotl (state.s1 * 5) 7 * 9
  let t := state.s1 <<< 17
  let s2' := state.s2 ^^^ state.s0
  let s3' := state.s3 ^^^ state.s1
  let s1' := state.s1 ^^^ s2'
  let s0' := state.s0 ^^^ s3'
  let s2'' := s2' ^^^ t
  let s3'' := rotl s3' 45
  (result, { s0 := s0', s1 := s1', s2 := s2'', s3 := s3'' })

def initPrng (seed : UInt64) : PrngState :=
  let z0 := seed + 0x9e3779b97f4a7c15
  let z1 := (z0 ^^^ (z0 >>> 30)) * 0xbf58476d1ce4e5b9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94d049bb133111eb
  let s0 := z2 ^^^ (z2 >>> 31)
  let z3 := s0 + 0x9e3779b97f4a7c15
  let z4 := (z3 ^^^ (z3 >>> 30)) * 0xbf58476d1ce4e5b9
  let z5 := (z4 ^^^ (z4 >>> 27)) * 0x94d049bb133111eb
  let s1 := z5 ^^^ (z5 >>> 31)
  let z6 := s1 + 0x9e3779b97f4a7c15
  let z7 := (z6 ^^^ (z6 >>> 30)) * 0xbf58476d1ce4e5b9
  let z8 := (z7 ^^^ (z7 >>> 27)) * 0x94d049bb133111eb
  let s2 := z8 ^^^ (z8 >>> 31)
  let z9 := s2 + 0x9e3779b97f4a7c15
  let z10 := (z9 ^^^ (z9 >>> 30)) * 0xbf58476d1ce4e5b9
  let z11 := (z10 ^^^ (z10 >>> 27)) * 0x94d049bb133111eb
  let s3 := z11 ^^^ (z11 >>> 31)
  { s0, s1, s2, s3 }

def nextFloat01 (state : PrngState) : Float × PrngState :=
  let (bits, state') := nextUInt64 state
  let f := Float.ofNat (bits >>> 11).toNat / 9007199254740992.0  -- 2^53
  (f, state')

def nextFloatRange (state : PrngState) (lo hi : Float) : Float × PrngState :=
  let (f, state') := nextFloat01 state
  (lo + f * (hi - lo), state')

def randMatrix (state : PrngState) (n : Nat) (lo hi : Float) :
    LUDecomp.FloatMat.FMat × PrngState := Id.run do
  let mut s := state
  let mut rows : Array (Array Float) := #[]
  for _ in [:n] do
    let mut row : Array Float := #[]
    for _ in [:n] do
      let (v, s') := nextFloatRange s lo hi
      row := row.push v
      s := s'
    rows := rows.push row
  return (rows, s)

def randDiagDominant (state : PrngState) (n : Nat) (lo hi : Float) :
    LUDecomp.FloatMat.FMat × PrngState := Id.run do
  let (A, state') := randMatrix state n lo hi
  let mut A' := A
  for i in [:n] do
    let mut rowSum := 0.0
    for k in [:n] do
      rowSum := rowSum + (LUDecomp.FloatMat.get A i k).abs
    A' := LUDecomp.FloatMat.set A' i i (rowSum + 1.0)
  return (A', state')

def hilbertMatrix (n : Nat) : LUDecomp.FloatMat.FMat :=
  LUDecomp.FloatMat.fromFn n n fun i j =>
    1.0 / Float.ofNat (i + j + 1)

end Fuzz
