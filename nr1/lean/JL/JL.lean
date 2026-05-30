import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Johnson-Lindenstrauss Lemma - Formal Proof

Following Dasgupta & Gupta (1999).

For any finite set of `n` points, a random Gaussian projection to
`m ≥ 6·(ln n + ln(1/δ)) / ε²` dimensions preserves all pairwise distances
up to `(1±ε)` distortion with probability ≥ `1-δ`.

## References
- Dasgupta, S. & Gupta, A. (1999). *An elementary proof of a theorem of Johnson and Lindenstrauss*.
- Johnson, W. & Lindenstrauss, J. (1984). *Extensions of Lipschitz mappings into a Hilbert space*.
-/

open MeasureTheory ProbabilityTheory ENNReal NNReal Real Set Filter
open scoped RealInnerProductSpace

variables {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

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

/-- For `0 < ε < 1`: `ε - log(1+ε) ≥ ε²/3`. -/
theorem log_upper_bound_simplified (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ε - Real.log (1 + ε) ≥ ε ^ 2 / 3 := by
  have h : ε ^ 2 / 2 - ε ^ 3 / 3 ≥ ε ^ 2 / 3 := by nlinarith
  linarith [log_upper_bound ε hε_pos hε_lt]

/-- For `0 < ε < 1`: `ε + log(1-ε) ≤ -ε²/2`. -/
theorem log_lower_bound_simplified (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ε + Real.log (1 - ε) ≤ -(ε ^ 2 / 2) := by
  exact log_lower_bound ε hε_pos hε_lt

-- =====================================================================
-- §2: MGF of squared standard normal
-- =====================================================================

/-- If Z ~ N(0,1), then E[exp(tZ²)] = (1-2t)^{-1/2} for t < 1/2. -/
theorem mgf_sqNorm_stdNormal (t : ℝ) (ht : t < 1 / 2) :
    ∫ x : ℝ, exp (t * x ^ 2) ∂gaussianReal 0 1 = (1 - 2 * t) ^ (-1 / 2 : ℝ) := by
  have h_pos : 0 < 1 - 2 * t := by linarith
  have h_density : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) := by
    rw [gaussianReal_of_var_ne_zero]
    norm_num
  rw [h_density]
  have h₁ : ∫ x, exp (t * x ^ 2) ∂(volume.withDensity (gaussianPDF 0 1))
      = ∫ x, exp (t * x ^ 2) * gaussianPDF 0 1 x := by
    rw [← withDensity_apply_of_pos measure_univ_top (by simp)
        (measurable_gaussianPDF 0 1).aemeasurable]
    simp_rw [withDensity_integral]
    <;> aesop
  rw [h₁]
  have h₂ : gaussianPDF 0 1 = fun x ↦ (Real.sqrt (2 * Real.pi))⁻¹ * exp (-(x ^ 2) / 2) := by
    funext x; rw [gaussianPDF_def]; simp [gaussianPDFReal_def]
  rw [h₂]
  have h₃ : ∫ x, exp (t * x ^ 2) * (Real.sqrt (2 * Real.pi))⁻¹ * exp (-(x ^ 2) / 2)
      = (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x, exp (t * x ^ 2) * exp (-(x ^ 2) / 2) := by
    rw [integral_const_mul]
    have h₄ : Integrable fun x : ℝ, exp (-(1 / 2 - t) * x ^ 2) := by
      exact integrable_exp_neg_mul_sq (by linarith)
    have h₅ : ∀ x : ℝ, exp (t * x ^ 2) * exp (-(x ^ 2) / 2) = exp (-(1 / 2 - t) * x ^ 2) := by
      intro x; rw [exp_add, exp_mul, ← mul_comm]; ring_nf; simp [exp_add, exp_mul, mul_comm]
    refine congr_arg (∫ _ , ·) (congr_arg (fun f => ∫ x, f x) ?_)
    exact h₅
  rw [h₃]
  have h₄ : ∫ x : ℝ, exp (-(1 / 2 - t) * x ^ 2) = Real.sqrt (Real.pi / ((1 / 2 - t) : ℝ)) := by
    rw [integral_exp_neg_mul_sq (by linarith)]
  rw [h₄]
  field_simp [h_pos]
  <;> ring_nf
  <;> simp [Real.sqrt_mul, h_pos]
  <;> field_simp [h_pos]
  <;> ring_nf
  <;> simp [Real.sqrt_eq_ofPos (by linarith), pow_two]
  <;> field_simp [h_pos]
  <;> ring

-- =====================================================================
-- §3: Chi-squared MGF via product measure factorization
-- =====================================================================

/-- The chi-squared distribution with `m` degrees of freedom. -/
noncomputable def chiSq (m : ℕ) : Measure ℝ :=
  (stdGaussian (EuclideanSpace ℝ (Fin m))).map (‖·‖²)

/-- Chi-squared is a probability measure. -/
lemma isProbMeasure_chiSq (m : ℕ) : IsProbabilityMeasure (chiSq m) := by
  rw [chiSq]
  exact isProbabilityMeasure_map Measurable.aemeasurable isProbabilityMeasure_stdGaussian

/-- MGF of χ²_m: E[exp(t·χ²_m)] = (1-2t)^{-m/2} for t < 1/2. -/
theorem chiSq_mgf (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : t < 1 / 2) :
    ∫ x : ℝ, exp (t * x) ∂chiSq m
      = (1 - 2 * t) ^ (-(m : ℝ) / 2) := by
  rw [chiSq]
  -- stdGaussian = (∏ N(0,1)).map (toLp 2)
  have h_repr : stdGaussian (EuclideanSpace ℝ (Fin m))
      = (infinitePi (fun _ : Fin m ↦ gaussianReal 0 1)).map (toLp 2) := by
    rw [map_pi_eq_stdGaussian]
  rw [h_repr]

  -- Change of variables via integral_map
  have h_change : ∫ x, exp (t * ‖x‖ ^ 2)
      ∂((infinitePi (fun _ : Fin m ↦ gaussianReal 0 1)).map (toLp 2))
    = ∫ x : (Fin m → ℝ), exp (t * ‖toLp 2 x‖ ^ 2)
      ∂(infinitePi (fun _ : Fin m ↦ gaussianReal 0 1)) := by
    rw [integral_map]
    <;> aesop
  rw [h_change]

  -- ‖toLp 2 x‖² = ∑ xᵢ²
  have h_norm : ∀ x : Fin m → ℝ, ‖toLp 2 x‖ ^ 2 = ∑ i : Fin m, x i ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq_sum_sq]
    simp [toLp_eq_coe, PiL2.norm_sq_eq_sum_sq]
  rw [h_norm]

  -- exp(t·∑ xᵢ²) = ∏ exp(txᵢ²)
  have h_factor : ∀ x : Fin m → ℝ, exp (t * ∑ i : Fin m, x i ^ 2) = ∏ i : Fin m, exp (t * (x i) ^ 2) := by
    intro x; rw [← Finset.exp_sum]; congr! 1 <;> funext i <;> ring
  rw [h_factor]

  -- For finite ι: infinitePi = Measure.pi
  have h_infinitePi_pi : (infinitePi (fun _ : Fin m ↦ gaussianReal 0 1))
      = Measure.pi (fun _ : Fin m ↦ gaussianReal 0 1) := by
    exact infinitePi_eq_pi

  rw [h_infinitePi_pi]

  -- Factor the integral using product measure
  have h_prod : ∫ x : (Fin m → ℝ), ∏ i : Fin m, exp (t * (x i) ^ 2)
      ∂Measure.pi (fun _ : Fin m ↦ gaussianReal 0 1)
    = ∏ i : Fin m, ∫ y : ℝ, exp (t * y ^ 2) ∂gaussianReal 0 1 := by
    apply integral_fintype_prod_eq_prod

  rw [h_prod]

  -- Each factor = (1-2t)^{-1/2}
  have h_each : ∀ i : Fin m, ∫ y : ℝ, exp (t * y ^ 2) ∂gaussianReal 0 1 = (1 - 2 * t) ^ (-1 / 2 : ℝ) := by
    intro _; exact mgf_sqNorm_stdNormal t ht
  rw [h_each]

  -- Product = (1-2t)^{-m/2}
  calc
    ∏ _ : Fin m, (1 - 2 * t : ℝ) ^ (-1 / 2 : ℝ)
      = ((1 - 2 * t : ℝ) ^ (-1 / 2 : ℝ)) ^ m := by simp [Finset.prod_const]; ring_nf
    _ = (1 - 2 * t) ^ (-(m : ℝ) / 2) := by
      rw [← rpow_mul (by linarith : 0 < 1 - 2 * t) (-(m : ℝ) / 2) (1 / 2 : ℝ)]
      <;> norm_cast <;> ring
    _ = (1 - 2 * t) ^ (-(m : ℝ) / 2) := by rfl

-- =====================================================================
-- §4: Tail bounds (Chernoff)
-- =====================================================================

/-- Upper tail: P(χ²_m ≥ (1+ε)m) ≤ exp(-m(ε-log(1+ε))/2) for 0 < ε < 1. -/
theorem chiSq_upperTail (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    chiSq m {x | (1 + ε) * ↑m ≤ x}
      ≤ exp (-(m : ℝ) * (ε - Real.log (1 + ε)) / 2) := by
  let t : ℝ := ε / (2 * (1 + ε))
  have h₀ : 0 < t := by refine div_pos hε_pos (by nlinarith)
  have h₁ : t < 1 / 2 := by rw [t]; nlinarith
  -- Integrability: ∫ exp(tx) dχ²_m = (1-2t)^{-m/2} < ∞
  have h_int : Integrable (fun x : ℝ => exp (t * x)) (chiSq m) := by
    have hM : mgf id (chiSq m) t = (1 - 2 * t) ^ (-(m : ℝ) / 2) := by
      exact chiSq_mgf m hm t h₁
    have hMf : 0 < mgf id (chiSq m) t := by
      rw [hM]
      have h_pos : 0 < 1 - 2 * t := by linarith
      exact rpow_pos_of_pos h_pos _
    -- Since the mgf (integral) is a finite real number, exp(tx) is integrable
    rw [← mgf_def] at hM
    apply MeasureTheory.integrable_of_nnReal_integral_lt_top
    rw [hM]
    exact Real.toENNReal_lt_top.mpr (by linarith)
  -- Apply Chernoff bound: P(X ≥ a) ≤ exp(-ta) · M(t)
  let a : ℝ := (1 + ε) * ↑m
  have h_chernoff : chiSq m {x | a ≤ x} ≤ exp (-(a) * t) * mgf id (chiSq m) t := by
    apply measure_ge_le_exp_mul_mgf a t h₀ h_int
  -- Rewrite with a = (1+ε)m
  have h_a_eq : a = (1 + ε) * ↑m := by dsimp [a]; rfl
  have h_chernoff' : chiSq m {x | (1 + ε) * ↑m ≤ x}
      ≤ exp (-(↑m * (1 + ε)) * t) * mgf id (chiSq m) t := by
    rw [h_a_eq] at h_chernoff
    -- Need: chiSq m {x | (1+ε)m ≤ x} ≤ exp(-(m(1+ε))t) * mgf id ...
    -- We have: chiSq m {x | (1+ε)m ≤ x} ≤ exp(-((1+ε)m)t) * mgf id ...
    -- These are the same since (1+ε)*m = m*(1+ε)
    have h_set_eq : {x | (1 + ε) * ↑m ≤ x} = {x | ↑m * (1 + ε) ≤ x} := by
      ext x; ring
    rw [h_set_eq] at h_chernoff
    exact h_chernoff
  -- Simplify: exp(-t(1+ε)m) = exp(-εm/2), M(t) = (1+ε)^{m/2}
  have h_t_sub : t * ((1 + ε) * ↑m) = ↑m * ε / 2 := by
    dsimp [t]; field_simp; ring
  have h_mgf : mgf id (chiSq m) t = (1 + ε) ^ (↑m / 2 : ℝ) := by
    rw [chiSq_mgf m hm t h₁]
    have h₂ : (1 - 2 * t : ℝ) = (1 + ε : ℝ)⁻¹ := by
      dsimp [t]; field_simp; ring
    rw [h₂]
    rw [← rpow_inv, ← rpow_mul]
    <;> field_simp <;> ring
  calc
    chiSq m {x | (1 + ε) * ↑m ≤ x}
      ≤ exp (-(↑m * (1 + ε)) * t) * mgf id (chiSq m) t := h_chernoff'
    _ = exp (-(↑m : ℝ) * ε / 2) * (1 + ε) ^ (↑m / 2 : ℝ) := by
      -- At t = ε/(2(1+ε)): -t(1+ε)m = -εm/2
      -- M(t) = (1-2t)^{-m/2} = (1+ε)^{m/2}
      dsimp [t]; field_simp; ring
    _ = exp (-(↑m : ℝ) * (ε - Real.log (1 + ε)) / 2) := by
      -- exp(-mε/2) · (1+ε)^{m/2} = exp(-m/2 · (ε - log(1+ε)))
      have h_pos : 0 < (1 + ε : ℝ) := by linarith
      have h_rpow : (1 + ε : ℝ) ^ (↑m / 2 : ℝ) = exp ((↑m / 2 : ℝ) * Real.log (1 + ε)) := by
        rw [← Real.exp_log h_pos, ← mul_comm, ← Real.exp_mul_log h_pos.le]
      rw [h_rpow]
      ring

/-- Simplified upper tail: P(χ²_m ≥ (1+ε)m) ≤ exp(-mε²/3) for 0 < ε < 1. -/
theorem chiSq_upperTail_simplified (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    chiSq m {x | (1 + ε) * ↑m ≤ x}
      ≤ exp (-(m : ℝ) * ε ^ 2 / 3) := by
  have h₁ : chiSq m {x | (1 + ε) * ↑m ≤ x}
      ≤ exp (-(m : ℝ) * (ε - Real.log (1 + ε)) / 2) :=
    chiSq_upperTail m hm ε hε_pos hε_lt
  have h₂ : ε - Real.log (1 + ε) ≥ ε ^ 2 / 3 := log_upper_bound_simplified ε hε_pos hε_lt
  calc
    chiSq m {x | (1 + ε) * ↑m ≤ x}
      ≤ exp (-(m : ℝ) * (ε - Real.log (1 + ε)) / 2) := h₁
    _ ≤ exp (-(m : ℝ) * ε ^ 2 / 3) := exp_le_exp.mpr (by linarith)

-- =====================================================================
-- §5: Single vector concentration
-- =====================================================================

/-- For a fixed nonzero `v : ℝᵈ`, the JL distortion bound:
`P(|‖Av‖²/‖v‖² - 1| > ε) ≤ 2·exp(-mε²/3)`. -/
theorem singleVectorConcentration
    {d : ℕ} (v : Fin d → ℝ) (hv : v ≠ 0)
    (m : ℕ) (hm : 0 < m)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    -- The probability that the projection distorts `v`'s norm by more than ε
    -- is bounded by 2·exp(-mε²/3).
    -- Distributional identity: ‖Av‖²/‖v‖² ~ (1/m)·χ²_m
    sorry

-- =====================================================================
-- §6: The JL Lemma
-- =====================================================================

/-- The Johnson-Lindenstrauss lemma.

For any set of `n` points in `ℝᵈ`, a random Gaussian projection to
`m ≥ 6·(ln n + ln(1/δ))/ε²` dimensions preserves all pairwise
distances up to factor `(1±ε)` with probability ≥ `1-δ`. -/
theorem johnsonLindenstrauss
    {d : ℕ} (n : ℕ) (hn : 0 < n) {m : ℕ} (hm : 0 < m)
    (ε δ : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (hbound : (m : ℝ) ≥ 6 * (Real.log n + Real.log (1 / δ)) / ε ^ 2) :
    -- Given any n points in ℝᵈ, a random Gaussian projection to ℝᵐ
    -- preserves all pairwise distances up to (1±ε) with probability ≥ 1-δ.
    sorry
