/-!
# Randomized SVD — Formalization

This library formalizes the randomized SVD algorithm from
Halko, Martinsson, Tropp (2011) "Finding Structure with Randomness".

The formalization includes:
- Matrix operations (multiplication, transpose, norms)
- Random Gaussian sampling
- Modified Gram-Schmidt QR decomposition
- Jacobi eigenvalue algorithm
- The randomized SVD algorithm (Pass 1-2)
- Low-rank approximation

Most theorems are stated as axioms (sorry) — the goal is to
establish the *correctness skeleton* that can later be proved.
-/

import RandomizedSVD.Matrix
import RandomizedSVD.QR
import RandomizedSVD.Eigen
import RandomizedSVD.RandomizedSVD
import RandomizedSVD.LowRankApprox
import RandomizedSVD.AccuracyBounds
