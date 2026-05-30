# Chi-Squared Tail Bounds via Chernoff Method

## The Chernoff Method

For any random variable `X` and any `t > 0`:

$$P(X \geq a) \leq \inf_{t > 0} \exp(-ta) \cdot E[\exp(tX)]$$

Similarly, for `t < 0`:

$$P(X \leq a) \leq \inf_{t < 0} \exp(-ta) \cdot E[\exp(tX)]$$

## Upper Tail

For `Z ~ χ²_m` and `0 < ε < 1`:

$$P(Z \geq (1+\varepsilon)m) \leq \exp\left(-\frac{m}{2}(\varepsilon - \log(1+\varepsilon))\right)$$

### Proof

Apply Chernoff with `t = ε/(2(1+ε))`:

1. `0 < t < 1/2`: Check `ε/(2(1+ε)) < 1/2` which is `ε < 1+ε`, true for `ε > 0`.
2. `exp(-t·(1+ε)m) = exp(-εm/2)`
3. `E[exp(tZ)] = (1-2t)^{-m/2} = (1+ε)^{m/2}` since `1-2t = 1 - ε/(1+ε) = (1+ε)^{-1}`
4. Product: `exp(-εm/2) · (1+ε)^{m/2} = exp(-m/2 · (ε - log(1+ε)))`

### Simplified form

Using `ε - log(1+ε) ≥ ε²/3`:

$$P(Z \geq (1+\varepsilon)m) \leq \exp\left(-\frac{m\varepsilon^2}{3}\right)$$

---

## Lower Tail

For `Z ~ χ²_m` and `0 < ε < 1` (with `ε < 1/2` for the standard approach):

$$P(Z \leq (1-\varepsilon)m) \leq \exp\left(-\frac{m}{2}(\varepsilon + \log(1-\varepsilon))\right)$$

### Proof

Apply Chernoff with `t = ε/(2(1-ε))`:

1. `0 < t`: Check `ε < 1`, satisfied.
2. `t < 1/2`: Check `ε/(2(1-ε)) < 1/2` which is `ε < 1-ε` i.e. `ε < 1/2`.
3. `exp(t·(1-ε)m) = exp(εm/2)`
4. `E[exp(-tZ)] = (1+2t)^{-m/2} = (1-ε)^{m/2}` since `1+2t = 1 + ε/(1-ε) = (1-ε)^{-1}`
5. Product: `exp(εm/2) · (1-ε)^{m/2} = exp(m/2 · (ε + log(1-ε)))`

### Simplified form

Using `ε + log(1-ε) ≤ -ε²/2`:

$$P(Z \leq (1-\varepsilon)m) \leq \exp\left(-\frac{m\varepsilon^2}{4}\right)$$

---

## Lean 4 Implementation

```lean
theorem chiSq_upperTail (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    chiSq m {x | (1 + ε) * ↑m ≤ x} ≤ exp (-(m : ℝ) * (ε - Real.log (1 + ε)) / 2)

theorem chiSq_upperTail_simplified (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    (chiSq m {x | (1 + ε) * ↑m ≤ x}).toReal ≤ exp (-(m : ℝ) * ε ^ 2 / 3)

theorem chiSq_lowerTail (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    chiSq m {x | x ≤ (1 - ε) * ↑m} ≤ exp (-(m : ℝ) * (ε + Real.log (1 - ε)) / 2)

theorem chiSq_lowerTail_simplified (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε_pos : 0 < ε)
    (hε_half : ε ≤ 1 / 2) :
    (chiSq m {x | x ≤ (1 - ε) * ↑m}).toReal ≤ exp (-(m : ℝ) * ε ^ 2 / 3)
```

The implementation uses:
- `measure_ge_le_exp_mul_mgf`: Chernoff upper tail bound from mathlib4
- `measure_le_le_exp_mul_mgf`: Chernoff lower tail bound from mathlib4
- `chiSq_mgf`: MGF of chi-squared
- `log_upper_bound` / `log_lower_bound`: Taylor bounds from §2
