/-!
# Test Matrix Generation

Helper functions to create test matrices for randomized SVD verification.
-/

import RandomizedSVD

namespace RandomizedSVD.Tests

/-- Generate a rank-k matrix: A = U_k * diag(s) * V_k^T.
    U_k and V_k have orthonormal columns.
    Singular values: s[i] = 10^(k-1-i) for i = 0..k-1.
    (This gives singular values [100, 10, 1, ...] for k=3.) -/
def makeRankKMatrix {m n k : ℕ} (m : ℕ) (n : ℕ) (k : ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  -- In practice: generate random orthonormal U and V, construct A
  -- Here: abstract over the construction
  sorry

/-- Generate a random Gaussian matrix. -/
def makeGaussianMatrix {m n : ℕ} (m : ℕ) (n : ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  -- In practice: sample from N(0, 1)
  sorry

/-- Generate a matrix with slow-decaying singular values. -/
def makeSlowDecayMatrix {m n : ℕ} (m : ℕ) (n : ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  -- Singular values decay as 1/i
  sorry

/-- Generate a signal+noise matrix: A = rank-k signal + ε * random noise. -/
def makeSignalNoiseMatrix {m n : ℕ} (m : ℕ) (n : ℕ) (k : ℕ) (ε : ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  -- A = U_k diag(s) V_k^T + ε * G
  sorry

end RandomizedSVD.Tests
