import QRDecomp.Matrix
import Mathlib.Data.Rat.Defs

/-!
# QR Decomposition (Modified Gram-Schmidt)

Implements A = QR decomposition over ℚ using unnormalized Modified Gram-Schmidt.
Q columns are orthogonal (not orthonormal) to avoid square roots in exact arithmetic.
R is upper triangular with R[k][k] = 1 (norms absorbed into Q).
-/

namespace QRDecomp

/-- Result of QR decomposition. -/
structure QRResult (n : ℕ) (α : Type*) where
  Q : Matrix (Fin n) (Fin n) α
  R : Matrix (Fin n) (Fin n) α
  singular : Bool

/-- Squared norm of a vector over ℚ: ∑ v[i]². -/
def normSq {n : ℕ} (v : Fin n → ℚ) : ℚ :=
  dotProduct v v

/-- State during QR decomposition. -/
structure QRState (n : ℕ) where
  Q : Matrix (Fin n) (Fin n) ℚ
  R : Matrix (Fin n) (Fin n) ℚ
  singular : Bool

/-- Perform one step of Modified Gram-Schmidt at column k.
    Orthogonalizes Q column k against columns 0..k-1.
    Stores projection coefficients in R[j][k] for j < k.
    Sets R[k][k] = 1 (unnormalized convention). -/
def qrStep {n : ℕ} [NeZero n] (s : QRState n) (k : Fin n) : QRState n :=
  -- Extract the current column k
  let vk := getCol s.Q k
  -- Orthogonalize against previous columns
  let result := (List.finRange n).foldl
    (fun (acc : (Fin n → ℚ) × (Matrix (Fin n) (Fin n) ℚ)) (j : Fin n) =>
      if j.val < k.val then
        let (v, R) := acc
        let qj := getCol s.Q j
        let nsq := normSq qj
        if nsq == 0 then acc
        else
          let coeff := dotProduct qj v / nsq
          let v' := subVec v (scaleVec coeff qj)
          let R' := setEntry R j k coeff
          (v', R')
      else acc)
    (vk, s.R)
  let (v', R') := result
  -- Check if the residual is zero (singular)
  let nsq := normSq v'
  if nsq == 0 then
    { Q := s.Q, R := R', singular := true }
  else
    -- Set R[k][k] = 1 (unnormalized: norm is in Q column)
    let R'' := setEntry R' k k 1
    -- Store the orthogonalized column back
    let Q' := setCol s.Q k v'
    { Q := Q', R := R'', singular := false }

/-- Recursive helper for QR decomposition. Processes columns k..n-1. -/
def qrDecomposeAux {n : ℕ} [NeZero n] (s : QRState n) (k : ℕ) (hk : k ≤ n) :
    QRState n :=
  if heq : k = n then s
  else if s.singular then s
  else
    have hlt : k < n := Nat.lt_of_le_of_ne hk heq
    qrDecomposeAux (qrStep s ⟨k, hlt⟩) (k + 1) (by omega)
termination_by n - k

/-- QR decomposition using Modified Gram-Schmidt.
    Returns Q with orthogonal columns and upper triangular R with unit diagonal,
    such that A = Q * R. -/
def qrDecompose {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℚ) :
    QRResult n ℚ :=
  let init : QRState n :=
    { Q := A
      R := fun i j => if i = j then 1 else 0
      singular := false }
  let result := qrDecomposeAux init 0 (Nat.zero_le n)
  -- Ensure R is strictly upper triangular below diagonal
  let R := fun i j =>
    if i.val > j.val then 0
    else result.R i j
  { Q := result.Q
    R := R
    singular := result.singular }

/-! ## Helper lemmas for proofs -/

/-- qrDecomposeAux unfold: at k = n, returns state unchanged. -/
@[simp]
theorem qrDecomposeAux_eq {n : ℕ} [NeZero n] (s : QRState n) (hk : n ≤ n) :
    qrDecomposeAux s n hk = s := by
  unfold qrDecomposeAux; simp

/-- qrDecomposeAux on singular state returns state unchanged. -/
theorem qrDecomposeAux_singular {n : ℕ} [NeZero n] (s : QRState n)
    (k : ℕ) (hk : k ≤ n) (hs : s.singular = true) :
    qrDecomposeAux s k hk = s := by
  unfold qrDecomposeAux
  split <;> simp_all

/-- The singular flag of qrDecomposeAux result. -/
theorem qrDecomposeAux_singular_preserved {n : ℕ} [NeZero n] (s : QRState n)
    (k : ℕ) (hk : k ≤ n) (hs : s.singular = true) :
    (qrDecomposeAux s k hk).singular = true := by
  rw [qrDecomposeAux_singular s k hk hs]
  exact hs

end QRDecomp
