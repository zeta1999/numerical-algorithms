# Taylor Bounds for log(1+ε) and log(1-ε)

## Lemma 1: Upper bound on log(1+ε)

For `0 < ε < 1`:

$$\varepsilon - \log(1+\varepsilon) \geq \frac{\varepsilon^2}{2} - \frac{\varepsilon^3}{3}$$

### Proof

Since `1/(1+x) ≤ 1 - x + x²` for `x ∈ [0, ε]` (because `1 ≤ (1-x+x²)(1+x) = 1+x³`, which holds for `x ≥ 0`), we have:

$$\varepsilon - \log(1+\varepsilon) = \int_0^\varepsilon \left(1 - \frac{1}{1+x}\right)dx \geq \int_0^\varepsilon (x - x^2)dx = \frac{\varepsilon^2}{2} - \frac{\varepsilon^3}{3}$$

### Corollary: Simplified form

$$\varepsilon - \log(1+\varepsilon) \geq \frac{\varepsilon^2}{3}$$

because `ε²/2 - ε³/3 = ε²(1/2 - ε/3) ≥ ε²(1/2 - 1/3) = ε²/3` for `0 < ε < 1`.

---

## Lemma 2: Upper bound on log(1-ε)

For `0 < ε < 1`:

$$\varepsilon + \log(1-\varepsilon) \leq -\frac{\varepsilon^2}{2}$$

Equivalently:

$$-\varepsilon - \log(1-\varepsilon) \geq \frac{\varepsilon^2}{2}$$

### Proof

Since `1/(1-x) ≥ 1 + x` for `x ∈ [0, ε]` (because `1 ≥ (1+x)(1-x) = 1-x²`, which holds for `|x| ≤ 1`), we have:

$$\varepsilon + \log(1-\varepsilon) = -\int_0^\varepsilon \left(\frac{1}{1-x} - 1\right)dx \leq -\int_0^\varepsilon x\,dx = -\frac{\varepsilon^2}{2}$$

### Corollary: Simplified form

For `0 < ε ≤ 1/2`:

$$\varepsilon + \log(1-\varepsilon) \leq -\frac{\varepsilon^2}{3}$$

because `-ε²/2 ≤ -ε²/3` for `ε > 0`.

---

## Lean 4 Implementation

All four lemmas are proved in `JL.lean` using integral comparisons:

- `log_upper_bound`: `ε - log(1+ε) ≥ ε²/2 - ε³/3`
- `log_lower_bound`: `ε + log(1-ε) ≤ -ε²/2`
- `log_upper_bound_simplified`: `ε - log(1+ε) ≥ ε²/3`
- `log_lower_bound_simplified`: `ε + log(1-ε) ≤ -ε²/2`
