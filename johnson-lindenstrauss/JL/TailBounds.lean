import JL.ChiSq
import JL.LogBounds

/-!
# JL §4 — Chernoff tail bounds for `χ²_m`

Upper and lower deviation bounds for the chi-squared distribution, obtained from the
MGF (`chiSq_mgf`) by the Chernoff method at the optimal `t`.  All probabilities are on
the real side via `Measure.real` (`μ.real s = (μ s).toReal`).

  * `chiSq_upperTail`            `P(χ²_m ≥ (1+ε)m) ≤ exp(-(m/2)(ε - log(1+ε)))`
  * `chiSq_lowerTail`            `P(χ²_m ≤ (1-ε)m) ≤ exp( (m/2)(ε + log(1-ε)))`
  * `chiSq_upperTail_simplified` `… ≤ exp(-m ε²/12)`
  * `chiSq_lowerTail_simplified` `… ≤ exp(-m ε²/12)`
-/

open MeasureTheory ProbabilityTheory Real Set

namespace JL

/-- `exp(t·x)` is integrable w.r.t. `χ²_m` for `t < 1/2`
(its MGF is finite and nonzero, so the integrand cannot be non-integrable). -/
lemma integrable_exp_mul_chiSq (m : ℕ) {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => rexp (t * x)) (chiSq m) := by
  by_contra h
  have h0 : mgf id (chiSq m) t = 0 := by
    rw [mgf]; exact integral_undef h
  rw [chiSq_mgf m t ht] at h0
  exact (Real.rpow_pos_of_pos (by linarith : (0:ℝ) < 1 - 2 * t) _).ne' h0

/-- **Upper tail.** `P(χ²_m ≥ (1+ε)m) ≤ exp(-(m/2)(ε - log(1+ε)))` for `0 < ε < 1`. -/
theorem chiSq_upperTail (m : ℕ) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    (chiSq m).real {x | (1 + ε) * (m : ℝ) ≤ x}
      ≤ rexp (-(m : ℝ) * (ε - Real.log (1 + ε)) / 2) := by
  have h1pe : (0 : ℝ) < 1 + ε := by linarith
  have h1pe' : (1 : ℝ) + ε ≠ 0 := by linarith
  set t : ℝ := ε / (2 * (1 + ε)) with ht_def
  have h0 : 0 < t := div_pos hε_pos (by linarith)
  have h12 : t < 1 / 2 := by
    rw [ht_def, div_lt_iff₀ (by positivity)]; nlinarith
  have hpos : (0 : ℝ) < 1 - 2 * t := by linarith
  have h_int := integrable_exp_mul_chiSq m h12
  have hch := measure_ge_le_exp_mul_mgf (X := id) (μ := chiSq m) ((1 + ε) * (m : ℝ)) h0.le h_int
  simp only [id_eq] at hch
  rw [chiSq_mgf m t h12] at hch
  refine hch.trans ?_
  -- exp(-t(1+ε)m) · (1-2t)^(-m/2) = exp(-(m/2)(ε - log(1+ε)))
  rw [Real.rpow_def_of_pos hpos, ← Real.exp_add]
  apply le_of_eq
  congr 1
  have hbase : 1 - 2 * t = (1 + ε)⁻¹ := by rw [ht_def]; field_simp; ring
  rw [hbase, Real.log_inv, ht_def]
  field_simp
  ring

/-- **Lower tail.** `P(χ²_m ≤ (1-ε)m) ≤ exp((m/2)(ε + log(1-ε)))` for `0 < ε < 1`. -/
theorem chiSq_lowerTail (m : ℕ) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    (chiSq m).real {x | x ≤ (1 - ε) * (m : ℝ)}
      ≤ rexp ((m : ℝ) * (ε + Real.log (1 - ε)) / 2) := by
  have h1me : (0 : ℝ) < 1 - ε := by linarith
  have h1me' : (1 : ℝ) - ε ≠ 0 := by linarith
  set t : ℝ := -(ε / (2 * (1 - ε))) with ht_def
  have h0 : t < 0 := by rw [ht_def]; simp only [neg_neg_iff_pos, Left.neg_neg_iff]; positivity
  have h12 : t < 1 / 2 := by linarith
  have hpos : (0 : ℝ) < 1 - 2 * t := by
    rw [ht_def]; have : 0 < ε / (2 * (1 - ε)) := by positivity
    linarith
  have h_int := integrable_exp_mul_chiSq m h12
  have hch := measure_le_le_exp_mul_mgf (X := id) (μ := chiSq m) ((1 - ε) * (m : ℝ)) h0.le h_int
  simp only [id_eq] at hch
  rw [chiSq_mgf m t h12] at hch
  refine hch.trans ?_
  rw [Real.rpow_def_of_pos hpos, ← Real.exp_add]
  apply le_of_eq
  congr 1
  have hbase : 1 - 2 * t = (1 - ε)⁻¹ := by rw [ht_def]; field_simp; ring
  rw [hbase, Real.log_inv, ht_def]
  field_simp

/-- **Simplified upper tail:** `P(χ²_m ≥ (1+ε)m) ≤ exp(-m ε²/12)` for `0 < ε < 1`. -/
theorem chiSq_upperTail_simplified (m : ℕ) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    (chiSq m).real {x | (1 + ε) * (m : ℝ) ≤ x}
      ≤ rexp (-(m : ℝ) * ε ^ 2 / 12) := by
  refine (chiSq_upperTail m ε hε_pos hε_lt).trans (Real.exp_le_exp.mpr ?_)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have := mul_le_mul_of_nonneg_left (log_upper_bound_simplified hε_pos hε_lt) hm
  linarith

/-- **Simplified lower tail:** `P(χ²_m ≤ (1-ε)m) ≤ exp(-m ε²/12)` for `0 < ε < 1`. -/
theorem chiSq_lowerTail_simplified (m : ℕ) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    (chiSq m).real {x | x ≤ (1 - ε) * (m : ℝ)}
      ≤ rexp (-(m : ℝ) * ε ^ 2 / 12) := by
  refine (chiSq_lowerTail m ε hε_pos hε_lt).trans (Real.exp_le_exp.mpr ?_)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have := mul_le_mul_of_nonneg_left (log_lower_bound_simplified hε_pos hε_lt) hm
  linarith

end JL
