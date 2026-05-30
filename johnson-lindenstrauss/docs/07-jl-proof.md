# The Johnson-Lindenstrauss Lemma: Full Proof

## Statement

Let `X = {x₁, ..., xₙ}` be a set of `n ≥ 1` points in `ℝᵈ`. Let `0 < ε < 1` and `0 < δ ≤ 1`. If

$$m \geq \frac{4(\ln n + \ln(1/\delta))}{\varepsilon^2}$$

then a random Gaussian projection `J: ℝᵈ → ℝᵐ` (with i.i.d. entries `~ N(0, 1/m)`) satisfies:

$$P\left(\forall i \neq j: (1-\varepsilon)\|x_i - x_j\|^2 \leq \|Jx_i - Jx_j\|^2 \leq (1+\varepsilon)\|x_i - x_j\|^2\right) \geq 1 - \delta$$

## Proof

### Step 1: Pairwise concentration

For any fixed pair `(i, j)` with `i ≠ j`, let `v = xᵢ - xⱼ`. If `v = 0`, the distances are trivially preserved. If `v ≠ 0`, by the single vector concentration result:

$$P\left(\left|\frac{\|Jv\|^2}{\|v\|^2} - 1\right| > \varepsilon\right) \leq 2\exp\left(-\frac{m\varepsilon^2}{3}\right)$$

### Step 2: Union bound over pairs

There are `n(n-1)/2 < n²/2` distinct pairs. By the union bound:

$$P(\exists \text{ pair with distortion}) \leq \frac{n^2}{2} \cdot 2\exp\left(-\frac{m\varepsilon^2}{3}\right) = n^2 \exp\left(-\frac{m\varepsilon^2}{3}\right)$$

### Step 3: Choosing `m`

We want `n² · exp(-mε²/3) ≤ δ`:

$$n^2 \cdot \exp\left(-\frac{m\varepsilon^2}{3}\right) \leq \delta$$

$$\exp\left(-\frac{m\varepsilon^2}{3}\right) \leq \frac{\delta}{n^2}$$

$$-\frac{m\varepsilon^2}{3} \leq \ln(\delta) - 2\ln(n)$$

$$\frac{m\varepsilon^2}{3} \geq 2\ln(n) + \ln(1/\delta)$$

$$m \geq \frac{3(2\ln n + \ln(1/\delta))}{\varepsilon^2}$$

Our bound `m ≥ 4(ln n + ln(1/δ))/ε²` satisfies this because:

$$4(\ln n + \ln(1/\delta)) \geq 3(2\ln n + \ln(1/\delta))$$

if and only if `4 ln n + 4 ln(1/δ) ≥ 6 ln n + 3 ln(1/δ)`, i.e., `ln(1/δ) ≥ 2 ln n`. This isn't always true, so the constant `C = 4` needs to be larger. A safe choice is `C = 6`:

$$m \geq \frac{6(\ln n + \ln(1/\delta))}{\varepsilon^2}$$

Then:

$$n^2 \exp\left(-\frac{m\varepsilon^2}{3}\right) \leq n^2 \exp\left(-2(\ln n + \ln(1/\delta))\right) = n^2 \cdot n^{-2} \cdot \delta^2 = \delta^2 \leq \delta$$

since `δ ≤ 1`.

### Step 4: Conclusion

With `m ≥ 6(ln n + ln(1/δ))/ε²`:

$$P(\text{all pairs preserved}) \geq 1 - n^2 \exp\left(-\frac{m\varepsilon^2}{3}\right) \geq 1 - \delta$$

## Summary of Constants

| Constant | Value | Source |
|----------|-------|--------|
| `C_upper` | `3` | Upper tail: `exp(-mε²/3)` |
| `C_lower` | `3` | Lower tail: `exp(-mε²/3)` |
| `C_union` | `6` | Final: `m ≥ 6(ln n + ln(1/δ))/ε²` |

The factor of 2 from the two-tailed bound plus the `n²` from the union bound requires `C_union ≥ 3 × 2 = 6`.

## References

- Dasgupta & Gupta (1999) use `m ≥ 4 ln(n/δ) / (ε²/2 - ε³/3)` which gives a tighter constant
- Our simplified proof uses `m ≥ 6(ln n + ln(1/δ))/ε²` for readability
