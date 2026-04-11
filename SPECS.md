
# Numerical Algorithms

Each algorithm is implemented in both Lean4 and F* (fstar).

Correctness is checked with:
- unit tests
- formal methods (proofs + axioms verified by testing)
- fuzzing

Each algorithm includes:
- linear system solver (Ax = b)
- sensitivity analysis (numerical errors and precision)

## nr1: LU Decomposition

- Doolittle LU with partial pivoting
- Lean4: exact (ℚ) + Float paths
- F*: fraction-free integer arithmetic

## nr2: QR Decomposition

- Modified Gram-Schmidt
- Lean4: exact (ℚ, unnormalized) + Float (normalized) paths
- F*: fraction-free integer arithmetic
- Additional metrics: orthogonality loss, reconstruction error
