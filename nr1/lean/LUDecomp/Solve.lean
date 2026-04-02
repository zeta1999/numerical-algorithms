import LUDecomp.LU

/-!
# Linear System Solver via LU Decomposition

Solves Ax = b by:
1. Decomposing PA = LU
2. Solving Ly = Pb (forward substitution)
3. Solving Ux = y (back substitution)
-/

namespace LUDecomp

/-- Forward substitution: solve Ly = b where L is unit lower triangular.
    Uses List.finRange to iterate with proper Fin indices. -/
def forwardSub {n : ℕ} (L : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    Fin n → ℚ :=
  let arr := (List.finRange n).foldl
    (fun (acc : Array ℚ) (idx : Fin n) =>
      let sum := (List.finRange n).foldl
        (fun (s : ℚ) (jdx : Fin n) =>
          if jdx.val < idx.val then s + L idx jdx * (acc[jdx.val]!)
          else s)
        0
      acc.set! idx.val (b idx - sum))
    (Array.replicate n 0)
  fun k => arr[k.val]!

/-- Back substitution: solve Ux = y where U is upper triangular.
    Returns `none` if a diagonal entry is zero. -/
def backSub {n : ℕ} (U : Matrix (Fin n) (Fin n) ℚ) (y : Fin n → ℚ) :
    Option (Fin n → ℚ) :=
  let result := (List.finRange n).reverse.foldl
    (fun (state : Option (Array ℚ)) (idx : Fin n) =>
      match state with
      | none => none
      | some acc =>
        let sum := (List.finRange n).foldl
          (fun (s : ℚ) (jdx : Fin n) =>
            if jdx.val > idx.val then s + U idx jdx * (acc[jdx.val]!)
            else s)
          0
        let diag := U idx idx
        if diag == 0 then none
        else some (acc.set! idx.val ((y idx - sum) / diag)))
    (some (Array.replicate n 0))
  match result with
  | none => none
  | some arr => some (fun k => arr[k.val]!)

/-- Solve the linear system Ax = b using LU decomposition.
    Returns `none` if A is singular. -/
def solveLU {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℚ)
    (b : Fin n → ℚ) : Option (Fin n → ℚ) :=
  let lu := luDecompose A
  if lu.singular then none
  else
    let pb := applyPerm lu.P b
    let y := forwardSub lu.L pb
    backSub lu.U y

end LUDecomp
