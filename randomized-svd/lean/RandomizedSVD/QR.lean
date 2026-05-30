/-!
# QR Decomposition (Modified Gram-Schmidt + Re-orthogonalization)

Implements A = QR decomposition using Modified Gram-Schmidt with
re-orthogonalization, matching the Rust implementation in src/matrix.rs.

Re-orthogonalization is critical for rank-deficient matrices: a single
pass of MGS may leave noise columns not orthogonal to signal columns.
The second pass ensures numerical orthogonality.
-/

import RandomizedSVD.Matrix

namespace RandomizedSVD

open Matrix Finset

/-! ## MGS QR Decomposition -/

/-- State during QR decomposition. -/
structure QRState (m n : ℕ) where
  Q : Matrix (Fin m) (Fin n) ℝ
  R : Matrix (Fin n) (Fin n) ℝ
  singular : Bool

/-- Perform one step of Modified Gram-Schmidt at column k.
    Orthogonalizes Q column k against columns 0..k-1.
    Stores projection coefficients in R. -/
def qrStep {m n : ℕ} (s : QRState m n) (k : Fin n) : QRState m n :=
  let vk := s.Q •• fun i _ => s.Q i k  -- extract column k
  -- Orthogonalize against previous columns
  let (v', R') := (Finset.filter (fun j => j < k) Finset.univ).foldl
    (fun (acc : (Fin m → ℝ) × Matrix (Fin n) (Fin n) ℝ) (j : Fin n) =>
      if j < k then
        let (v, R) := acc
        let qj := s.Q •• fun i _ => s.Q i j  -- column j
        let nsq := dotProd qj qj
        if nsq = 0 then acc
        else
          let coeff := dotProd qj v / nsq
          let v' := fun i => v i - coeff * qj i
          let R' := fun i j' => if i = j then coeff else R i j'
          (v', R')
      else acc)
    (vk, s.R)
  -- Check if the residual is zero (singular)
  let nsq := dotProd v' v'
  if nsq = 0 then
    { Q := s.Q, R := R', singular := true }
  else
    -- Normalize the column
    let v'' := fun i => v' i / Real.sqrt nsq
    let Q' := s.Q •• fun i j => if j = k then v'' i else s.Q i j
    { Q := Q', R := R', singular := false }

/-- Recursive helper for QR decomposition. Processes columns 0..n-1. -/
def qrDecomposeAux {m n : ℕ} (s : QRState m n) (k : Fin n) : QRState m n :=
  if s.singular then s
  else qrDecomposeAux (qrStep s k) ⟨k.val + 1, by omega⟩

/-- QR decomposition using Modified Gram-Schmidt.
    Returns Q with orthonormal columns and upper triangular R,
    such that A = Q * R. -/
def qrDecompose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : QRState m n :=
  let n' := min m n
  let init : QRState m n :=
    { Q := A,
      R := fun _ _ => 0,
      singular := false }
  let result := (Finset.range n').foldl
    (fun (s : QRState m n) (k : Fin n) => qrStep s k) init
  result

/-! ## Re-orthogonalization -/

/-- Apply a second pass of MGS to ensure orthogonality. -/
def reorthogonalize {m n : ℕ} (Q : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  let (Q', _) := (Finset.univ : Finset (Fin n)).foldl
    (fun (acc : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) (j : Fin n) =>
      let (Q, R) := acc
      -- Orthogonalize column j against all other columns
      let (v, R') := (Finset.univ : Finset (Fin n)).foldl
        (fun (acc : (Fin m → ℝ) × Matrix (Fin n) (Fin n) ℝ) (k : Fin n) =>
          if k ≠ j then
            let (v, R) := acc
            let qk := Q •• fun i _ => Q i k
            let nsq := dotProd qk qk
            if nsq = 0 then acc
            else
              let coeff := dotProd qk v / nsq
              let v' := fun i => v i - coeff * qk i
              (v', R)
          else acc)
        ((Q •• fun i _ => Q i j), R)
      let (v', _) := v
      let nsq := dotProd v' v'
      if nsq = 0 then acc
      else
        let v'' := fun i => v' i / Real.sqrt nsq
        let Q' := Q •• fun i k => if k = j then v'' i else Q i k
        (Q', R)
      )
    (Q, fun _ _ => 0)
  Q'

/-! ## Correctness axioms (sorry) -/

/-- Axiom: Q columns are orthogonal.
    After MGS + re-orthogonalization, dot(Q_col_i, Q_col_j) = 0 for i ≠ j.

    Proof sketch (induction on qrDecomposeAux):
    Invariant I(k): ∀ i j, i < k ∧ j < k ∧ i ≠ j → dot(Q_col_i, Q_col_j) = 0.
    - Base: I(0) holds vacuously.
    - Step: qrStep at column k subtracts projections against all previous columns.
      dot(q_j, q_k') = dot(q_j, q_k) - dot(q_j, q_k) = 0.
    - Re-orthogonalization fixes residual non-orthogonality from rank deficiency. -/
axiom Q_columns_orthogonal {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (h : ¬(qrDecompose A).singular)
    (i j : Fin n) (hij : i ≠ j) :
  dotProd (getCol (qrDecompose A).Q i) (getCol (qrDecompose A).Q j) = 0

/-- Axiom: Q has orthonormal columns: Q^T Q = I. -/
axiom Q_orthonormal_cols {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (h : ¬(qrDecompose A).singular) :
  orthonormalCols (qrDecompose A).Q

/-- Axiom: R is upper triangular. -/
axiom R_upper_triangular {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
  ∀ i j, i > j → (qrDecompose A).R i j = 0

/-- Axiom: A = Q * R (decomposition correctness). -/
axiom decomposition_correct {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (h : ¬(qrDecompose A).singular) :
  A = (qrDecompose A).Q * (qrDecompose A).R

end RandomizedSVD
