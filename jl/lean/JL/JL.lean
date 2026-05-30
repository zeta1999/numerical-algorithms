import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Johnson-Lindenstrauss Lemma

Following Dasgupta & Gupta (1999).

For any finite set of `n` points in a metric space, a random Gaussian projection
to `m ≥ 4·(ln n + ln(1/δ)) / ε²` dimensions preserves all pairwise distances
up to `(1±ε)` distortion with probability ≥ `1-δ`.

## References
- Dasgupta, S. & Gupta, A. (1999). *An elementary proof of a theorem of Johnson and Lindenstrauss*.
- Johnson, W. & Lindenstrauss, J. (1984). *Extensions of Lipschitz mappings into a Hilbert space*.
-/

open MeasureTheory ProbabilityTheory ENNReal NNReal Real Set Filter
open scoped RealInnerProductSpace

-- =====================================================================
-- §1: Taylor bounds for log
-- =====================================================================

/-- For `0 < ε < 1`: `ε - log(1+ε) ≥ ε²/2 - ε³/3`. -/
theorem log_upper_bound (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ε - Real.log (1 + ε) ≥ ε ^ 2 / 2 - ε ^ 3 / 3 := by
  have h₁ : ∀ x ∈ Icc (0 : ℝ) ε, 1 / (1 + x) ≤ 1 - x + x ^ 2 := by
    intro x hx
    have h₂ : 0 < 1 + x := by linarith
    rw [div_le_iff h₂]
    nlinarith [mul_nonneg (zero_le_one.add (le_of_lt hx.1)) (sq_nonneg x)]
  calc
    ε - Real.log (1 + ε) = ∫ x in (0 : ℝ)..ε, (1 - 1 / (1 + x)) := by
      have h₃ : ∫ x in (0 : ℝ)..ε, 1 / (1 + x) = Real.log (1 + ε) - Real.log 1 := by
        rw [← integral_log]
      simp only [Real.log_one, sub_zero, h₃]
      <;> ring
    _ ≥ ∫ x in (0 : ℝ)..ε, (x - x ^ 2) := by
      apply integral_le_integral
      intro x hx
      have h₂ : 0 < 1 + x := by linarith [hx.1, hx.2]
      rw [le_div_iff h₂]
      nlinarith [sq_nonneg x]
    _ = ε ^ 2 / 2 - ε ^ 3 / 3 := by
      ring_nf; field_simp; ring

/-- For `0 < ε < 1`: `ε + log(1-ε) ≤ -ε²/2`. -/
theorem log_lower_bound (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ε + Real.log (1 - ε) ≤ -(ε ^ 2 / 2) := by
  have h₁ : ∀ x ∈ Icc (0 : ℝ) ε, 1 / (1 - x) ≥ 1 + x := by
    intro x hx
    have h₂ : 0 < 1 - x := by linarith
    rw [ge_iff_le, le_div_iff h₂]
    nlinarith
  calc
    ε + Real.log (1 - ε)
    = -∫ x in (0 : ℝ)..ε, (1 / (1 - x) - 1) := by
      have h₂ : ∫ x in (0 : ℝ)..ε, 1 / (1 - x) = -Real.log (1 - ε) + Real.log 1 := by
        rw [← integral_log]
        <;> field_simp
      simp [h₂, Real.log_one]
      <;> ring
    _ ≤ -∫ x in (0 : ℝ)..ε, x := by
      apply integral_le_integral
      intro x hx
      have h₂ : 0 < 1 - x := by linarith [hx.2]
      rw [ge_iff_le, le_div_iff h₂]
      nlinarith
    _ = -ε ^ 2 / 2 := by ring

/-- Simplified: `ε - log(1+ε) ≥ ε²/3` for `0 < ε < 1`. -/
theorem log_upper_bound_simplified (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ε - Real.log (1 + ε) ≥ ε ^ 2 / 3 := by
  -- ε²/2 - ε³/3 = ε²(1/2 - ε/3) ≥ ε²(1/2 - 1/3) = ε²/3 for 0 < ε < 1
  have h : ε ^ 2 / 2 - ε ^ 3 / 3 ≥ ε ^ 2 / 3 := by
    nlinarith
  linarith [log_upper_bound ε hε_pos hε_lt]

/-- Simplified: `ε + log(1-ε) ≤ -ε²/3` for `0 < ε < 1/2`. -/
theorem log_lower_bound_simplified (ε : ℝ) (hε_pos : 0 < ε) (hε_half : ε ≤ 1 / 2) :
    ε + Real.log (1 - ε) ≤ -ε ^ 2 / 3 := by
  -- -ε²/2 ≤ -ε²/3 for ε > 0
  nlinarith [log_lower_bound ε hε_pos (by linarith)]

-- =====================================================================
-- §2: MGF of squared standard normal
-- =====================================================================

/-- If Z ~ N(0,1), then E[exp(tZ²)] = (1-2t)^{-1/2} for t < 1/2.
Proof: ∫ exp(tx²) · (2π)^{-1/2} · exp(-x²/2) dx
     = (2π)^{-1/2} · ∫ exp(-(1-2t)x²/2) dx
     = (2π)^{-1/2} · √(2π/(1-2t))
     = (1-2t)^{-1/2}. -/
theorem mgf_sqNorm_stdNormal (t : ℝ) (ht : t < 1 / 2) :
    ∫ x : ℝ, exp (t * x ^ 2) ∂gaussianReal 0 1 = (1 - 2 * t) ^ (-1 / 2 : ℝ) := by
  have h_pos : 0 < 1 - 2 * t := by linarith
  have h_pos_half : 0 < (1 - 2 * t) / 2 := by linarith
  -- gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) since var = 1 ≠ 0
  have h_density : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) := by
    rw [gaussianReal_of_var_ne_zero]
    norm_num
  rw [h_density]
  -- The integral with respect to the density measure equals ∫ f·density dvolume
  have h₁ : ∫ x, exp (t * x ^ 2) ∂(volume.withDensity (gaussianPDF 0 1))
      = ∫ x, exp (t * x ^ 2) * gaussianPDF 0 1 x := by
    -- Use withDensity_integral
    rw [← withDensity_apply_of_pos measure_univ_top (by simp)
        (measurable_gaussianPDF 0 1).aemeasurable]
    simp_rw [withDensity_integral]
    <;> aesop
  rw [h₁]
  -- gaussianPDF 0 1 x = (2π)^{-1/2} · exp(-x²/2)
  have h₂ : gaussianPDF 0 1 = fun x ↦ (Real.sqrt (2 * Real.pi))⁻¹ * exp (-(x ^ 2) / 2) := by
    funext x; rw [gaussianPDF_def]; simp [gaussianPDFReal_def]
  rw [h₂]
  -- Factor out the constant (2π)^{-1/2}
  have h₃ : ∫ x, exp (t * x ^ 2) * (Real.sqrt (2 * Real.pi))⁻¹ * exp (-(x ^ 2) / 2)
      = (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x, exp (t * x ^ 2) * exp (-(x ^ 2) / 2) := by
    rw [integral_const_mul]
    -- Integrability: exp(tx²)·exp(-x²/2) = exp(-(1-2t)x²/2) is integrable since (1-2t)/2 > 0
    have h₄ : Integrable fun x : ℝ, exp (-(1 / 2 - t) * x ^ 2) := by
      exact integrable_exp_neg_mul_sq (by linarith)
    -- exp(tx²) * exp(-x²/2) = exp(-(1/2-t)x²)
    have h₅ : ∀ x : ℝ, exp (t * x ^ 2) * exp (-(x ^ 2) / 2) = exp (-(1 / 2 - t) * x ^ 2) := by
      intro x
      rw [exp_add, exp_mul, ← mul_comm]
      <;> ring_nf
      <;> simp [exp_add, exp_mul, mul_comm]
    refine congr_arg (∫ _ , ·) (congr_arg (fun f => ∫ x, f x) ?_)
    exact h₅
  rw [h₃]
  -- Now compute ∫ exp(-(1/2-t)x²) dx = √(2π/(1-2t))
  have h₄ : ∫ x : ℝ, exp (-(1 / 2 - t) * x ^ 2) = Real.sqrt (Real.pi / ((1 / 2 - t) : ℝ)) := by
    rw [integral_exp_neg_mul_sq (by linarith)]
  rw [h₄]
  -- (2π)^{-1/2} · √(π/(1/2-t)) = (2π)^{-1/2} · √π · (1/2-t)^{-1/2}
  -- = (2π)^{-1/2} · √π · 2^{1/2} · (1-2t)^{-1/2}
  -- = 2^{-1/2} · π^{-1/2} · π^{1/2} · 2^{1/2} · (1-2t)^{-1/2}
  -- = (1-2t)^{-1/2}
  field_simp [h_pos, h_pos_half]
  <;> ring_nf
  <;> simp [Real.sqrt_mul, h_pos, h_pos_half]
  <;> field_simp [h_pos]
  <;> ring_nf
  <;> simp [Real.sqrt_eq_ofPos (by linarith), pow_two]
  <;> field_simp [h_pos]
  <;> ring

-- =====================================================================
-- §3: Chi-squared MGF
-- =====================================================================

/-- The chi-squared distribution with `m` degrees of freedom: the distribution of `‖g‖²`
where `g ~ N(0, I_m)`. -/
def chiSq (m : ℕ) : Measure ℝ :=
  (stdGaussian (EuclideanSpace ℝ (Fin m))).map (‖·‖²)

/-- Chi-squared is a probability measure. -/
lemma isProbMeasure_chiSq (m : ℕ) : IsProbabilityMeasure (chiSq m) := by
  rw [chiSq]
  exact isProbabilityMeasure_map Measurable.aemeasurable isProbabilityMeasure_stdGaussian

/-- MGF of χ²_m: E[exp(t·χ²_m)] = (1-2t)^{-m/2} for t < 1/2.

Proof: χ²_m = ‖g‖² = ∑ᵢ Xᵢ² where Xᵢ are i.i.d. N(0,1).
So E[exp(t·χ²_m)] = ∏ᵢ E[exp(t·Xᵢ²)] = (1-2t)^{-m/2}.

We prove this by using the product measure structure of `stdGaussian`.
The key fact: `stdGaussian (EuclideanSpace ℝ (Fin m))` is the pushforward
of the product measure `(∏_{i : Fin m} gaussianReal 0 1)` under the
orthonormal basis map, and the squared norm is preserved. -/
theorem chiSq_mgf (m : ℕ) (t : ℝ) (ht : t < 1 / 2) :
    mgf id (chiSq m) t = (1 - 2 * t) ^ (-(m : ℝ) / 2) := by
  -- We need to compute ∫ exp(t·‖x‖²) d(stdGaussian ℝᵐ).
  -- The key insight: stdGaussian ℝᵐ = pushforward of (∏ N(0,1)) under an
  -- orthonormal basis map. Since the basis is orthonormal, ‖∑ xᵢeᵢ‖² = ∑ xᵢ².
  -- So the MGF factors as a product of 1D integrals.
  --
  -- Formal approach: use the fact that stdGaussian is defined as
  -- (∏ gaussianReal 0 1).map (fun x ↦ ∑ xᵢ · eᵢ)
  -- where {eᵢ} is the standard orthonormal basis.
  --
  -- Under this map, ‖∑ xᵢ·eᵢ‖² = ∑ xᵢ² (Parseval's identity).
  -- So: chiSq m = (∏ N(0,1)).map (fun x ↦ ∑ xᵢ²).
  -- And: ∫ exp(t·(∑ xᵢ²)) d(∏ N(0,1)) = ∏ ∫ exp(t·xᵢ²) dN(0,1).
  --
  -- Each ∫ exp(t·xᵢ²) dN(0,1) = (1-2t)^{-1/2} by mgf_sqNorm_stdNormal.
  -- So the product = (1-2t)^{-m/2}.

  -- Step 1: Express stdGaussian as pushforward of product measure
  -- stdGaussian E = (infinitePi (fun _ : Fin (finrank E) ↦ gaussianReal 0 1)).map (fun x ↦ ∑ xᵢ · eᵢ)
  -- We need Fin (finrank E) ≃ Fin m for E = EuclideanSpace ℝ (Fin m).

  have h_finrank : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin m))) ≃ Fin m := by
    rw [Module.finrank_real_euclideanSpace]
    apply Equiv.eSymm
    exact FinsumEquivFinsumSymm (m := m)

  -- Use the representation of stdGaussian
  have h_stdGaussian_repr :
      stdGaussian (EuclideanSpace ℝ (Fin m)) =
        (infinitePi (fun _ : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin m))) ↦ gaussianReal 0 1))
          .map (fun x : (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin m))) → ℝ)
            ↦ ∑ i, x i • (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin m)) i)) := by
    rfl  -- follows from the definition of stdGaussian

  -- After reindexing by Fin m via h_finrank:
  have h_product_eq :
      (infinitePi (fun _ : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin m))) ↦ gaussianReal 0 1))
          .map (fun x ↦ ∑ i, x i • (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin m)) i))
      = (infinitePi (fun _ : Fin m ↦ gaussianReal 0 1)).map
          (fun y : (Fin m → ℝ) ↦ ∑ j : Fin m, y j • (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin m)) (h_finrank.symm j))) := by
    -- Reindex the product measure by Fin m via the equivalence
    sorry
  sorry

-- We'll revisit this with a different, more direct approach if needed.
-- For now, we state the theorem and move on to the tail bounds.

-- =====================================================================
-- §4: Tail bounds (Chernoff)
-- =====================================================================

/-- Upper tail: P(χ²_m ≥ (1+ε)m) ≤ exp(-m(ε - log(1+ε))/2).
Chosen at t = ε/(2(1+ε)). -/
theorem chiSq_upperTail (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    chiSq m {x | (1 + ε) * ↑m ≤ x}
      ≤ exp (-(m : ℝ) * (ε - Real.log (1 + ε)) / 2) := by
  -- P(X ≥ (1+ε)m) ≤ exp(-t(1+ε)m) · E[exp(tX)] for t ∈ (0, 1/2)
  -- Choose t = ε/(2(1+ε)). Check: 0 < t < 1/2 ✓
  -- exp(-t(1+ε)m) = exp(-εm/2)
  -- E[exp(tX)] = (1-2t)^{-m/2} = (1+ε)^{m/2}
  -- Product = exp(-εm/2) · (1+ε)^{m/2} = exp(-m/2 · (ε - log(1+ε)))
  sorry

/-- Simplified upper tail: P(χ²_m ≥ (1+ε)m) ≤ exp(-mε²/3) for 0 < ε < 1. -/
theorem chiSq_upperTail_simplified (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    chiSq m {x | (1 + ε) * ↑m ≤ x}
      ≤ exp (-(m : ℝ) * ε ^ 2 / 3) := by
  sorry

/-- Lower tail: P(χ²_m ≤ (1-ε)m) ≤ exp(-m(ε + log(1-ε))/2).
Chosen at t = ε/(2(1-ε)). -/
theorem chiSq_lowerTail (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    chiSq m {x | x ≤ (1 - ε) * ↑m}
      ≤ exp (-(m : ℝ) * (ε + Real.log (1 - ε)) / 2) := by
  -- P(X ≤ (1-ε)m) ≤ exp(t(1-ε)m) · E[exp(-tX)] for t > 0
  -- E[exp(-tX)] = (1+2t)^{-m/2} for t > 0
  -- Choose t = ε/(2(1-ε)). Then 1+2t = 1/(1-ε).
  -- exp(t(1-ε)m) = exp(εm/2)
  -- (1+2t)^{-m/2} = (1-ε)^{m/2}
  -- Product = exp(εm/2) · (1-ε)^{m/2} = exp(m/2 · (ε + log(1-ε)))
  sorry

/-- Simplified lower tail: P(χ²_m ≤ (1-ε)m) ≤ exp(-mε²/3) for 0 < ε < 1/2. -/
theorem chiSq_lowerTail_simplified (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε_pos : 0 < ε)
    (hε_half : ε ≤ 1 / 2) :
    chiSq m {x | x ≤ (1 - ε) * ↑m}
      ≤ exp (-(m : ℝ) * ε ^ 2 / 3) := by
  sorry

-- =====================================================================
-- §5: Single vector concentration
-- =====================================================================

/-- For a fixed nonzero vector `v`, the random projection `Av` satisfies:
`‖Av‖² / ‖v‖² ~ (1/m)·χ²_m`.

In the Gaussian model: `A` has entries `~ N(0, 1/m)`. For any fixed `v`:
`Av = (1/m) · Gᵀv` where `G` has i.i.d. `N(0,1)` entries.
`Gᵀv ~ N(0, ‖v‖²·I_m)`. So `‖Av‖² = (‖v‖²/m²) · χ²_m`.
Thus `‖Av‖² / ‖v‖² = (1/m) · (χ²_m/m)`... wait, let me be more careful.

Actually: A is m×d with Aᵢⱼ ~ N(0, 1/m). So the i-th row of A is ~ N(0, I_d/m).
For fixed v: (Av)ᵢ = rowᵢ(A) · v ~ N(0, ‖v‖²/m).
So Av ~ N(0, (‖v‖²/m)·I_m).
Thus ‖Av‖² / (‖v‖²/m) ~ χ²_m.
Equivalently: ‖Av‖² / ‖v‖² ~ (1/m)·χ²_m.
-/
theorem singleVectorDist
    {d : ℕ} (v : Fin d → ℝ) (hv : v ≠ 0) (m : ℕ) (hm : 0 < m) :
    -- The distribution of ‖Av‖² / ‖v‖² where A has i.i.d. N(0, 1/m) entries
    -- matches the distribution of (1/m) · ‖g‖² where g ~ N(0, I_m).
    -- And ‖g‖² ~ χ²_m.
    -- So ‖Av‖² / ‖v‖² ~ (1/m)·χ²_m.
    sorry

/-- For any fixed nonzero `v`, the JL distortion holds with exponential probability:
`P(|‖Av‖²/‖v‖² - 1| > ε) ≤ 2·exp(-mε²/3)`. -/
theorem singleVectorConcentration
    {d : ℕ} (v : Fin d → ℝ) (hv : v ≠ 0)
    (m : ℕ) (hm : 0 < m)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    -- P(‖Av‖² ∉ [(1-ε)‖v‖², (1+ε)‖v‖²]) ≤ 2·exp(-mε²/3)
    sorry

-- =====================================================================
-- §6: The JL Lemma
-- =====================================================================

/-- The Johnson-Lindenstrauss lemma.

For any set of `n` points in any metric space, there exists a map to
`ℝᵐ` where `m ≥ 4·(ln n + ln(1/δ))/ε²` that preserves all pairwise
distances up to factor `(1±ε)` with probability ≥ `1-δ`. -/
theorem johnsonLindenstrauss
    {d : ℕ} (n : ℕ) (hn : 0 < n) {m : ℕ} (hm : 0 < m)
    (ε δ : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (hbound : (m : ℝ) ≥ 4 * (Real.log n + Real.log (1 / δ)) / ε ^ 2) :
    -- Given any n points in ℝᵈ, a random Gaussian projection to ℝᵐ
    -- preserves all pairwise distances up to (1±ε) with probability ≥ 1-δ.
    sorry
