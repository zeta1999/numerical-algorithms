import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# JL §1 — Taylor / logarithm bounds

Elementary inequalities for `log(1 ± ε)`, obtained by integrating the pointwise
bound `1/(1+x) ≤ 1 - x + x²` (resp. `1 + x ≤ 1/(1-x)`) over `[0, ε]`.

These feed the Chernoff tail bounds: `ε - log(1+ε)` and `-(ε + log(1-ε))` are the
exponents, and we lower-bound them by `ε²/3`.
-/

open Real Set intervalIntegral MeasureTheory

namespace JL

/-- Pointwise bound: `1/(1+x) ≤ 1 - x + x²` for `0 ≤ x`. -/
lemma one_div_one_add_le {x : ℝ} (hx : 0 ≤ x) : 1 / (1 + x) ≤ 1 - x + x ^ 2 := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg hx hx) hx]

/-- Pointwise bound: `1 + x ≤ 1/(1-x)` for `0 ≤ x < 1`. -/
lemma one_add_le_one_div_one_sub {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    1 + x ≤ 1 / (1 - x) := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith [sq_nonneg x]

/-- `∫₀^ε 1/(1+x) dx = log(1+ε)` for `0 < ε`. -/
lemma integral_one_div_one_add {ε : ℝ} (hε : 0 < ε) :
    ∫ x in (0:ℝ)..ε, 1 / (1 + x) = Real.log (1 + ε) := by
  have h : ∫ x in (0:ℝ)..ε, 1 / (1 + x) = ∫ u in (1:ℝ)..(1 + ε), 1 / u := by
    have := intervalIntegral.integral_comp_add_left (fun u => 1 / u) (a := 0) (b := ε) 1
    simpa using this
  rw [h, integral_one_div]
  · rw [add_div, div_self (by norm_num : (1:ℝ) ≠ 0)]
    norm_num
  · -- 0 ∉ [[1, 1+ε]]
    rw [Set.uIcc_of_le (by linarith)]
    simp only [Set.mem_Icc, not_and, not_le]
    intro h0; linarith

/-- `ContinuousOn (fun x => 1/(1+x))` on `[0, ε]` (denominator is positive). -/
lemma continuousOn_one_div_one_add {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun x : ℝ => 1 / (1 + x)) (uIcc 0 ε) := by
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro x hx
  rw [Set.uIcc_of_le hε.le] at hx
  have : 0 ≤ x := hx.1
  linarith

/-- **Upper log bound.** For `0 < ε < 1`: `ε - log(1+ε) ≥ ε²/2 - ε³/3`. -/
theorem log_upper_bound {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ε - Real.log (1 + ε) ≥ ε ^ 2 / 2 - ε ^ 3 / 3 := by
  have hint1 : IntervalIntegrable (fun x : ℝ => 1 / (1 + x)) volume 0 ε :=
    (continuousOn_one_div_one_add hε_pos).intervalIntegrable
  have iiconst : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 ε :=
    continuous_const.intervalIntegrable 0 ε
  have iiid : IntervalIntegrable (fun x : ℝ => x) volume 0 ε :=
    continuous_id'.intervalIntegrable 0 ε
  have iisq : IntervalIntegrable (fun x : ℝ => x ^ 2) volume 0 ε :=
    (continuous_pow 2).intervalIntegrable 0 ε
  have hI1 : ∫ x in (0:ℝ)..ε, (1 - 1 / (1 + x)) = ε - Real.log (1 + ε) := by
    rw [intervalIntegral.integral_sub iiconst hint1,
      integral_one_div_one_add hε_pos]
    simp
  have hI2 : ∫ x in (0:ℝ)..ε, (x - x ^ 2) = ε ^ 2 / 2 - ε ^ 3 / 3 := by
    rw [intervalIntegral.integral_sub iiid iisq, integral_id, integral_pow]
    norm_num
  have hmono : ∫ x in (0:ℝ)..ε, (x - x ^ 2) ≤ ∫ x in (0:ℝ)..ε, (1 - 1 / (1 + x)) := by
    apply intervalIntegral.integral_mono_on hε_pos.le (iiid.sub iisq)
      (iiconst.sub hint1)
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have := one_div_one_add_le hx0
    linarith
  rw [hI1, hI2] at hmono
  linarith

/-- `∫₀^ε 1/(1-x) dx = -log(1-ε)` for `0 < ε < 1`. -/
lemma integral_one_div_one_sub {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∫ x in (0:ℝ)..ε, 1 / (1 - x) = -Real.log (1 - ε) := by
  have h : ∫ x in (0:ℝ)..ε, 1 / (1 - x) = ∫ u in (1 - ε)..(1:ℝ), 1 / u := by
    have := intervalIntegral.integral_comp_sub_left (fun u => 1 / u) (a := 0) (b := ε) 1
    simpa using this
  rw [h, integral_one_div]
  · rw [one_div, Real.log_inv]
  · rw [Set.uIcc_of_le (by linarith)]
    simp only [Set.mem_Icc, not_and, not_le]
    intro h0; linarith

/-- `ContinuousOn (fun x => 1/(1-x))` on `[0, ε]` for `ε < 1`. -/
lemma continuousOn_one_div_one_sub {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ContinuousOn (fun x : ℝ => 1 / (1 - x)) (uIcc 0 ε) := by
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro x hx
  rw [Set.uIcc_of_le hε.le] at hx
  have : x ≤ ε := hx.2
  have : x < 1 := lt_of_le_of_lt hx.2 hε1
  linarith

/-- **Lower log bound.** For `0 < ε < 1`: `ε + log(1-ε) ≤ -ε²/2`. -/
theorem log_lower_bound {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ε + Real.log (1 - ε) ≤ -(ε ^ 2 / 2) := by
  have hint1 : IntervalIntegrable (fun x : ℝ => 1 / (1 - x)) volume 0 ε :=
    (continuousOn_one_div_one_sub hε_pos hε_lt).intervalIntegrable
  have iiconst : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 ε :=
    continuous_const.intervalIntegrable 0 ε
  have iiid : IntervalIntegrable (fun x : ℝ => x) volume 0 ε :=
    continuous_id'.intervalIntegrable 0 ε
  have hI1 : ∫ x in (0:ℝ)..ε, (1 / (1 - x) - 1) = -(ε + Real.log (1 - ε)) := by
    rw [intervalIntegral.integral_sub hint1 iiconst,
      integral_one_div_one_sub hε_pos hε_lt]
    simp; ring
  have hI2 : ∫ x in (0:ℝ)..ε, x = ε ^ 2 / 2 := by
    rw [integral_id]; norm_num
  have hmono : ∫ x in (0:ℝ)..ε, x ≤ ∫ x in (0:ℝ)..ε, (1 / (1 - x) - 1) := by
    apply intervalIntegral.integral_mono_on hε_pos.le iiid
      (hint1.sub iiconst)
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hxε : x ≤ ε := hx.2
    have hx1 : x < 1 := lt_of_le_of_lt hxε hε_lt
    have := one_add_le_one_div_one_sub hx0 hx1
    linarith
  rw [hI1, hI2] at hmono
  linarith

/-- Simplified: `ε - log(1+ε) ≥ ε²/6` for `0 < ε < 1`.
(Note: the cleaner-looking `ε²/3` bound is **false** near `ε = 1`; `ε²/6` is the
sharpest constant of this form derivable from `log_upper_bound`, valid on all of `(0,1)`.) -/
theorem log_upper_bound_simplified {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ε - Real.log (1 + ε) ≥ ε ^ 2 / 6 := by
  have h : ε ^ 2 / 2 - ε ^ 3 / 3 ≥ ε ^ 2 / 6 := by
    nlinarith [mul_nonneg (sq_nonneg ε) (by linarith : (0:ℝ) ≤ 1 - ε)]
  linarith [log_upper_bound hε_pos hε_lt]

/-- Simplified: `ε + log(1-ε) ≤ -ε²/6` for `0 < ε < 1`. -/
theorem log_lower_bound_simplified {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ε + Real.log (1 - ε) ≤ -(ε ^ 2 / 6) := by
  have := log_lower_bound hε_pos hε_lt
  nlinarith [sq_nonneg ε]

end JL
