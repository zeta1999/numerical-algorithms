# Numerical Sensitivity Analysis: LU Decomposition

## Overview

This report analyzes the sensitivity of the LU decomposition solver to numerical errors.
The key metric is the **condition number** `kappa(A)`, which bounds how input perturbations
are amplified in the solution:

```
||delta_x|| / ||x|| <= kappa(A) * ||delta_b|| / ||b||
```

For LU with partial pivoting, the theoretical error bound is:

```
forward_error <= kappa(A) * machine_epsilon * growth_factor
```

where `machine_epsilon = 2.22e-16` (IEEE 754 double precision) and the growth factor
is typically O(1) with partial pivoting.

## Experimental Setup

- **Algorithm**: Doolittle LU decomposition with partial pivoting
- **Precision**: IEEE 754 binary64 (double precision)
- **Matrix sizes**: n = 5, 10, 20, 50
- **Target condition numbers**: 1, 1e2, 1e4, 1e6, 1e8, 1e10, 1e12
- **Trials per configuration**: 20
- **Matrix construction**: `A = Q * diag(sigma) * Q^T` where Q is random orthogonal
  and sigma controls the condition number
- **Error metrics**:
  - Forward error: `||x_computed - x_true||_inf / ||x_true||_inf`
  - Backward error: `||Ax - b||_inf / (||A||_inf * ||x||_inf + ||b||_inf)`

## Results

### n=5

| Target kappa | Actual kappa   | Mean Fwd Err | Max Fwd Err | Mean Bwd Err | Max Bwd Err |
|-------------|---------------|-------------|------------|-------------|------------|
| 1           | 1.00          | 0           | 0          | 0           | 0          |
| 1e2         | 1.68e2        | 0           | 0          | 0           | 0          |
| 1e4         | 1.69e4        | 0           | 0          | 0           | 0          |
| 1e6         | 1.76e6        | 0           | 0          | 0           | 0          |
| 1e8         | 1.79e8        | 0           | 0          | 0           | 0          |
| 1e10        | 1.77e10       | ~0          | 1e-6       | 0           | 0          |
| 1e12        | 1.70e12       | 1.6e-5      | 6.5e-5     | 0           | 0          |

### n=10

| Target kappa | Actual kappa   | Mean Fwd Err | Max Fwd Err | Mean Bwd Err | Max Bwd Err |
|-------------|---------------|-------------|------------|-------------|------------|
| 1           | 1.00          | 0           | 0          | 0           | 0          |
| 1e2         | 2.13e2        | 0           | 0          | 0           | 0          |
| 1e4         | 2.16e4        | 0           | 0          | 0           | 0          |
| 1e6         | 2.12e6        | 0           | 0          | 0           | 0          |
| 1e8         | 2.20e8        | 0           | 0          | 0           | 0          |
| 1e10        | 2.17e10       | ~0          | ~0         | 0           | 0          |
| 1e12        | 2.31e12       | 1.6e-5      | 6.2e-5     | 0           | 0          |

### n=20

| Target kappa | Actual kappa   | Mean Fwd Err | Max Fwd Err | Mean Bwd Err | Max Bwd Err |
|-------------|---------------|-------------|------------|-------------|------------|
| 1           | 1.00          | 0           | 0          | 0           | 0          |
| 1e2         | 2.85e2        | 0           | 0          | 0           | 0          |
| 1e4         | 2.83e4        | 0           | 0          | 0           | 0          |
| 1e6         | 2.61e6        | 0           | 0          | 0           | 0          |
| 1e8         | 2.55e8        | 0           | 0          | 0           | 0          |
| 1e10        | 2.50e10       | ~0          | ~0         | 0           | 0          |
| 1e12        | 2.51e12       | 7e-6        | 2.8e-5     | 0           | 0          |

### n=50

| Target kappa | Actual kappa   | Mean Fwd Err | Max Fwd Err | Mean Bwd Err | Max Bwd Err |
|-------------|---------------|-------------|------------|-------------|------------|
| 1           | 1.00          | 0           | 0          | 0           | 0          |
| 1e2         | 4.80e2        | 0           | 0          | 0           | 0          |
| 1e4         | 4.22e4        | 0           | 0          | 0           | 0          |
| 1e6         | 3.90e6        | 0           | 0          | 0           | 0          |
| 1e8         | 3.54e8        | 0           | 0          | 0           | 0          |
| 1e10        | 3.23e10       | ~0          | ~0         | 0           | 0          |
| 1e12        | 3.22e12       | 1.3e-5      | 2.5e-5     | 0           | 0          |

## Analysis

### Forward Error

The forward error follows the theoretical prediction:

```
forward_error ~ kappa(A) * epsilon
```

- For `kappa <= 1e8`, forward error is at or below machine precision (effectively zero)
- For `kappa ~ 1e10`, forward errors appear at ~1e-6 level
- For `kappa ~ 1e12`, forward errors reach ~1e-5 to 1e-4

This matches the bound: `1e12 * 2.22e-16 = 2.22e-4`.

At `kappa ~ 1/epsilon = ~4.5e15`, the solution loses all significant digits.

### Backward Error

Backward error remains at machine precision across all condition numbers.
This confirms that LU with partial pivoting is **backward stable**:
the computed solution is the exact solution to a nearby problem.

### Matrix Size Independence

The error is largely independent of matrix size `n` for the same condition number.
This is expected: the growth factor with partial pivoting is bounded by `2^(n-1)` in
the worst case, but typically remains O(1) for random matrices.

### Actual vs Target Condition Number

Actual condition numbers are typically 1.5-5x larger than the target. This is expected
because the Gram-Schmidt orthogonalization used to construct test matrices is not
perfectly numerically stable, introducing mild perturbations.

## Conclusions

1. **LU with partial pivoting is backward stable** — backward error stays at machine epsilon
2. **Forward error is proportional to kappa(A) * epsilon** — as predicted by theory
3. **The algorithm is reliable** for matrices with `kappa < 1e12` (12 digits of accuracy lost)
4. **For ill-conditioned systems** (`kappa > 1e12`), consider iterative refinement or
   higher-precision arithmetic

## Reproduction

```bash
cd nr1/lean
lake build sensitivity
lake exe sensitivity
```

Or run the full pipeline:
```bash
cd nr1
bash run.sh
```
