# MGF of Squared Standard Normal

## Theorem

If `Z ~ N(0,1)`, then for `t < 1/2`:

$$E[\exp(tZ^2)] = (1 - 2t)^{-1/2}$$

## Proof

The MGF is:

$$E[\exp(tZ^2)] = \int_{-\infty}^{\infty} \exp(tx^2) \cdot \frac{1}{\sqrt{2\pi}} \exp(-x^2/2)\,dx$$

Combine the exponents:

$$= \frac{1}{\sqrt{2\pi}} \int_{-\infty}^{\infty} \exp\left(-\frac{1-2t}{2} \cdot x^2\right)\,dx$$

This is a Gaussian integral with variance parameter `1/(1-2t)`. Using:

$$\int_{-\infty}^{\infty} \exp(-bx^2)\,dx = \sqrt{\frac{\pi}{b}}$$

with `b = (1-2t)/2`:

$$= \frac{1}{\sqrt{2\pi}} \cdot \sqrt{\frac{\pi}{(1-2t)/2}} = \frac{1}{\sqrt{2\pi}} \cdot \sqrt{\frac{2\pi}{1-2t}} = (1-2t)^{-1/2}$$

## Lean 4 Implementation

```lean
theorem mgf_sqNorm_stdNormal (t : ℝ) (ht : t < 1 / 2) :
    ∫ x : ℝ, exp (t * x ^ 2) ∂gaussianReal 0 1 = (1 - 2 * t) ^ (-1 / 2 : ℝ)
```

The implementation uses:
1. `gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1)` to express the integral w.r.t. Lebesgue measure
2. `gaussianPDF 0 1 = (2π)^{-1/2} · exp(-x²/2)`
3. `exp(tx²) · exp(-x²/2) = exp(-(1-2t)x²/2)` (combine exponents)
4. `integral_exp_neg_mul_sq`: `∫ exp(-bx²) dx = √(π/b)` for `b > 0`
5. Algebraic simplification to get `(1-2t)^{-1/2}`
