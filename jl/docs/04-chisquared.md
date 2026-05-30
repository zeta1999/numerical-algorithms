# Chi-Squared Distribution and MGF

## Definition

The chi-squared distribution with `m` degrees of freedom is defined as the distribution of `‖g‖²` where `g ~ N(0, I_m)` is a standard Gaussian vector in `ℝᵐ`:

$$\chi^2_m = \text{distribution of } \|g\|^2, \quad g \sim N(0, I_m)$$

In Lean: `chiSq m = (stdGaussian ℝᵐ).map ‖·‖²`

## MGF Theorem

For `t < 1/2`:

$$E[\exp(t \cdot \chi^2_m)] = (1 - 2t)^{-m/2}$$

### Proof

**Key observation**: `stdGaussian(ℝᵐ)` has the product measure structure:

$$\text{stdGaussian}(\mathbb{R}^m) = \left(\prod_{i=1}^{m} N(0,1)\right) \circ (\text{toLp } 2)^{-1}$$

This means the coordinates of a standard Gaussian in any orthonormal basis are i.i.d. `N(0,1)`.

**Step 1**: Write the squared norm as a sum: `‖g‖² = ∑ᵢ Xᵢ²` where `Xᵢ ~ N(0,1)` are independent.

**Step 2**: The MGF factors:

$$E[\exp(t \cdot \sum_i X_i^2)] = \prod_{i=1}^{m} E[\exp(t \cdot X_i^2)]$$

This follows from the product measure factorization lemma:

$$\int \prod_i f_i(x_i) \, d(\prod_i \mu_i) = \prod_i \int f_i \, d\mu_i$$

**Step 3**: Each factor uses the 1D result: `E[exp(t·Xᵢ²)] = (1-2t)^{-1/2}`

**Step 4**: The product is `(1-2t)^{-m/2}`:

$$\prod_{i=1}^{m} (1-2t)^{-1/2} = ((1-2t)^{-1/2})^m = (1-2t)^{-m/2}$$

## Lean 4 Implementation

```lean
theorem chiSq_mgf (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : t < 1 / 2) :
    ∫ x : ℝ, exp (t * x) ∂chiSq m = (1 - 2 * t) ^ (-(m : ℝ) / 2)
```

The proof uses:
- `map_pi_eq_stdGaussian`: `stdGaussian E = (∏ N(0,1)).map (toLp 2)`
- `integral_map`: change of variables for pushforward measures
- `EuclideanSpace.norm_sq_eq_sum_sq`: `‖x‖² = ∑ xᵢ²`
- `Finset.exp_sum`: `exp(∑ xᵢ) = ∏ exp(xᵢ)`
- `infinitePi_eq_pi`: `infinitePi = Measure.pi` for fintype
- `integral_fintype_prod_eq_prod`: product measure integral factorization
- `mgf_sqNorm_stdNormal`: 1D MGF computation
