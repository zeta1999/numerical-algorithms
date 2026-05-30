# Single Vector Concentration

## Statement

Let `v ∈ ℝᵈ` be nonzero. Let `A ∈ ℝ^{m×d}` have i.i.d. entries `Aᵢⱼ ~ N(0, 1/m)`. Then:

$$\frac{\|Av\|^2}{\|v\|^2} \sim \frac{1}{m} \cdot \chi^2_m$$

Moreover, for `0 < ε < 1`:

$$P\left(\left|\frac{\|Av\|^2}{\|v\|^2} - 1\right| > \varepsilon\right) \leq 2 \exp\left(-\frac{m\varepsilon^2}{3}\right)$$

## Proof

**Distributional identity**: For fixed `v` and random `A`:

- Each row `Aᵢ` of `A` is `~ N(0, I_d/m)`
- `(Av)ᵢ = Aᵢ · v ~ N(0, ‖v‖²/m)`
- So `Av ~ N(0, (‖v‖²/m) · I_m)`
- Therefore `‖Av‖² / (‖v‖²/m) ~ χ²_m`
- Equivalently: `‖Av‖² / ‖v‖² ~ (1/m) · χ²_m`

**Tail bound**: Using the chi-squared tail bounds:

$$P\left(\frac{\|Av\|^2}{\|v\|^2} > (1+\varepsilon)\right) = P(\chi^2_m > (1+\varepsilon)m) \leq \exp\left(-\frac{m\varepsilon^2}{3}\right)$$

$$P\left(\frac{\|Av\|^2}{\|v\|^2} < (1-\varepsilon)\right) = P(\chi^2_m < (1-\varepsilon)m) \leq \exp\left(-\frac{m\varepsilon^2}{3}\right)$$

(Both bounds use `exp(-mε²/3)` after simplification.)

By union bound:

$$P\left(\left|\frac{\|Av\|^2}{\|v\|^2} - 1\right| > \varepsilon\right) \leq 2\exp\left(-\frac{m\varepsilon^2}{3}\right)$$

## Lean 4 Implementation

```lean
theorem singleVectorConcentration
    {d : ℕ} (v : Fin d → ℝ) (hv : v ≠ 0)
    (m : ℕ) (hm : 0 < m)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    P {A : (Fin m → (Fin d → ℝ)) | ‖A v‖₂ ^ 2 ∉ (Set.Icc ((1 - ε) * ‖v‖₂ ^ 2) ((1 + ε) * ‖v‖₂ ^ 2))}
      ≤ 2 * exp (-(m : ℝ) * ε ^ 2 / 3)
```

The implementation uses:
- Distributional identity: `‖Av‖² / ‖v‖² ~ (1/m) · χ²_m`
- `chiSq_upperTail_simplified`: Upper tail bound
- `chiSq_lowerTail_simplified`: Lower tail bound
- Union bound: `P(A ∪ B) ≤ P(A) + P(B)`
