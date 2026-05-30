import JL.TailBounds

/-!
# JL §5 — Single-vector concentration

For a fixed nonzero `v ∈ ℝᵈ`, a Gaussian random projection `A` with i.i.d. `N(0,1/m)`
entries sends `v` to `Av ∼ N(0, (‖v‖²/m) I_m)`, so `‖Av‖² ∼ (‖v‖²/m)·χ²_m`.
We model this law as `projNormSq m v` and bound the distortion probability
`P(‖Av‖² ∉ [(1-ε)‖v‖², (1+ε)‖v‖²]) ≤ 2·exp(-m ε²/12)`.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace JL

/-- The law of `‖Av‖²` for a fixed nonzero `v`: a scaled chi-squared,
`(‖v‖²/m)·χ²_m`. -/
noncomputable def projNormSq (m : ℕ) {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) : Measure ℝ :=
  (chiSq m).map (fun z => (‖v‖ ^ 2 / m) * z)

instance isProbMeasure_projNormSq (m : ℕ) {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    IsProbabilityMeasure (projNormSq m v) := by
  rw [projNormSq]; exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Reduce the upper distortion event for `projNormSq` to a chi-squared tail. -/
lemma projNormSq_real_upper (m d : ℕ) (m_pos : 0 < m)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0) (ε : ℝ) :
    (projNormSq m v).real {y | (1 + ε) * ‖v‖ ^ 2 ≤ y}
      = (chiSq m).real {z | (1 + ε) * (m : ℝ) ≤ z} := by
  have hv2 : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv) 2
  have hmeas : MeasurableSet {y : ℝ | (1 + ε) * ‖v‖ ^ 2 ≤ y} :=
    measurableSet_le measurable_const measurable_id
  have hpre : (fun z => ‖v‖ ^ 2 / (m : ℝ) * z) ⁻¹' {y | (1 + ε) * ‖v‖ ^ 2 ≤ y}
      = {z | (1 + ε) * (m : ℝ) ≤ z} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [div_mul_eq_mul_div, le_div_iff₀ (show (0 : ℝ) < (m : ℝ) by exact_mod_cast m_pos)]
    constructor <;> intro h <;> nlinarith [h, hv2]
  have hmap : projNormSq m v {y | (1 + ε) * ‖v‖ ^ 2 ≤ y} = chiSq m {z | (1 + ε) * (m : ℝ) ≤ z} := by
    rw [projNormSq, Measure.map_apply (by fun_prop) hmeas, hpre]
  rw [Measure.real, Measure.real, hmap]

/-- Reduce the lower distortion event for `projNormSq` to a chi-squared tail. -/
lemma projNormSq_real_lower (m d : ℕ) (m_pos : 0 < m)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0) (ε : ℝ) :
    (projNormSq m v).real {y | y ≤ (1 - ε) * ‖v‖ ^ 2}
      = (chiSq m).real {z | z ≤ (1 - ε) * (m : ℝ)} := by
  have hv2 : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv) 2
  have hmeas : MeasurableSet {y : ℝ | y ≤ (1 - ε) * ‖v‖ ^ 2} :=
    measurableSet_le measurable_id measurable_const
  have hpre : (fun z => ‖v‖ ^ 2 / (m : ℝ) * z) ⁻¹' {y | y ≤ (1 - ε) * ‖v‖ ^ 2}
      = {z | z ≤ (1 - ε) * (m : ℝ)} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [div_mul_eq_mul_div, div_le_iff₀ (show (0 : ℝ) < (m : ℝ) by exact_mod_cast m_pos)]
    constructor <;> intro h <;> nlinarith [h, hv2]
  have hmap : projNormSq m v {y | y ≤ (1 - ε) * ‖v‖ ^ 2} = chiSq m {z | z ≤ (1 - ε) * (m : ℝ)} := by
    rw [projNormSq, Measure.map_apply (by fun_prop) hmeas, hpre]
  rw [Measure.real, Measure.real, hmap]

/-- **Single-vector concentration.**  The probability that the random projection
distorts `‖v‖²` by more than a factor `ε` is at most `2·exp(-m ε²/12)`. -/
theorem singleVectorConcentration (m d : ℕ) (m_pos : 0 < m)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    (projNormSq m v).real ({y | (1 + ε) * ‖v‖ ^ 2 ≤ y} ∪ {y | y ≤ (1 - ε) * ‖v‖ ^ 2})
      ≤ 2 * rexp (-(m : ℝ) * ε ^ 2 / 12) := by
  calc (projNormSq m v).real ({y | (1 + ε) * ‖v‖ ^ 2 ≤ y} ∪ {y | y ≤ (1 - ε) * ‖v‖ ^ 2})
      ≤ (projNormSq m v).real {y | (1 + ε) * ‖v‖ ^ 2 ≤ y}
          + (projNormSq m v).real {y | y ≤ (1 - ε) * ‖v‖ ^ 2} := measureReal_union_le _ _
    _ = (chiSq m).real {z | (1 + ε) * (m : ℝ) ≤ z}
          + (chiSq m).real {z | z ≤ (1 - ε) * (m : ℝ)} := by
        rw [projNormSq_real_upper m d m_pos v hv, projNormSq_real_lower m d m_pos v hv]
    _ ≤ rexp (-(m : ℝ) * ε ^ 2 / 12) + rexp (-(m : ℝ) * ε ^ 2 / 12) := by
        gcongr
        · exact chiSq_upperTail_simplified m ε hε_pos hε_lt
        · exact chiSq_lowerTail_simplified m ε hε_pos hε_lt
    _ = 2 * rexp (-(m : ℝ) * ε ^ 2 / 12) := by ring

end JL
