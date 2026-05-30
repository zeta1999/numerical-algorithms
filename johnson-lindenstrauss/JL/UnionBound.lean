import JL.Projection

/-!
# JL §6 — Union bound and the Johnson–Lindenstrauss lemma

We model the random Gaussian projection as `m` i.i.d. standard-Gaussian rows.
The key lemma `rowLaw_map_projSq` identifies the law of the projected squared
norm with `projNormSq`, reducing the per-pair distortion bound to the
already-proven single-vector concentration.  A union bound over the `≤ n²`
pairs then yields the Johnson–Lindenstrauss lemma.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace InnerProductSpace

namespace JL

/-- The law of an `m × d` Gaussian row-matrix: `m` i.i.d. standard Gaussian rows. -/
noncomputable def rowLaw (m d : ℕ) : Measure (Fin m → EuclideanSpace ℝ (Fin d)) :=
  Measure.pi (fun _ => stdGaussian (EuclideanSpace ℝ (Fin d)))

instance isProbMeasure_rowLaw (m d : ℕ) : IsProbabilityMeasure (rowLaw m d) := by
  rw [rowLaw]; infer_instance

/-- **Step 1.** The image of `stdGaussian` under the inner product `⟪v, ·⟫` is a
centered real Gaussian with variance `‖v‖²`. -/
lemma stdGaussian_map_inner {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun g => ⟪v, g⟫_ℝ)
      = gaussianReal 0 (‖v‖₊ ^ 2) := by
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    (innerSL ℝ v)
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm] at h
  have hcoe : (‖v‖ ^ 2 : ℝ).toNNReal = ‖v‖₊ ^ 2 := by
    rw [Real.toNNReal_pow (norm_nonneg v), norm_toNNReal]
  rw [hcoe] at h
  convert h using 2

/-- **Step 3.** `gaussianReal 0 (‖v‖₊²)` is the pushforward of `gaussianReal 0 1`
under multiplication by `‖v‖`. -/
lemma gaussianReal_normSq_eq_map {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    gaussianReal 0 (‖v‖₊ ^ 2) = (gaussianReal 0 1).map (fun y => ‖v‖ * y) := by
  rw [gaussianReal_map_const_mul ‖v‖]
  simp only [mul_zero, mul_one]
  congr 1

/-- **Step 5.** The pushforward of the product of standard real Gaussians under
`y ↦ ∑ yᵢ²` is the chi-squared law. -/
lemma pi_gaussianReal_map_sumSq_eq_chiSq (m : ℕ) :
    (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map (fun y => ∑ i, y i ^ 2)
      = chiSq m := by
  rw [chiSq, ← map_pi_eq_stdGaussian (ι := Fin m),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext y
  simp only [Function.comp_apply]
  exact (norm_toLp_sq m y).symm

/-- **Key lemma.** The law of the projected squared norm under `rowLaw` equals
the scaled chi-squared `projNormSq m v`. -/
lemma rowLaw_map_projSq (m d : ℕ) (v : EuclideanSpace ℝ (Fin d)) :
    (rowLaw m d).map (fun G => (1 / (m : ℝ)) * ∑ i, ⟪v, G i⟫_ℝ ^ 2) = projNormSq m v := by
  -- Decompose the scalar map through the coordinatewise inner products.
  have hf1 : Measurable (fun (G : Fin m → EuclideanSpace ℝ (Fin d)) (i : Fin m) => ⟪v, G i⟫_ℝ) := by
    apply measurable_pi_lambda
    intro i
    exact (innerSL ℝ v).continuous.measurable.comp (measurable_pi_apply i)
  have hf2 : Measurable (fun y : Fin m → ℝ => (1 / (m : ℝ)) * ∑ i, y i ^ 2) := by fun_prop
  have hsplit : (fun G : Fin m → EuclideanSpace ℝ (Fin d) => (1 / (m : ℝ)) * ∑ i, ⟪v, G i⟫_ℝ ^ 2)
      = (fun y : Fin m → ℝ => (1 / (m : ℝ)) * ∑ i, y i ^ 2)
        ∘ (fun G i => ⟪v, G i⟫_ℝ) := rfl
  rw [hsplit, ← Measure.map_map hf2 hf1]
  -- Step 1 + 2: the coordinatewise inner product map of the product measure.
  have hrow : (rowLaw m d).map (fun G i => ⟪v, G i⟫_ℝ)
      = Measure.pi (fun _ : Fin m => gaussianReal 0 (‖v‖₊ ^ 2)) := by
    rw [rowLaw]
    rw [Measure.pi_map_pi (μ := fun _ : Fin m => stdGaussian (EuclideanSpace ℝ (Fin d)))
      (f := fun _ => fun g => ⟪v, g⟫_ℝ)
      (fun _ => (innerSL ℝ v).continuous.measurable.aemeasurable)]
    congr 1
    ext1 i
    exact stdGaussian_map_inner v
  rw [hrow]
  -- Step 3: scaling.
  rw [show (fun _ : Fin m => gaussianReal 0 (‖v‖₊ ^ 2))
      = (fun _ : Fin m => (gaussianReal 0 1).map (fun y => ‖v‖ * y)) from
        funext (fun _ => gaussianReal_normSq_eq_map v)]
  rw [← Measure.pi_map_pi (fun _ => (by fun_prop : AEMeasurable (fun y : ℝ => ‖v‖ * y)
        (gaussianReal 0 1)))]
  rw [Measure.map_map hf2 (by fun_prop)]
  -- Now compute: the composed map is `y ↦ (‖v‖²/m) * ∑ yᵢ²`, factoring through sumSq.
  rw [show (fun y : Fin m → ℝ => (1 / (m : ℝ)) * ∑ i, y i ^ 2)
        ∘ (fun (x : Fin m → ℝ) (i : Fin m) => ‖v‖ * x i)
      = (fun z => (‖v‖ ^ 2 / (m : ℝ)) * z) ∘ (fun y : Fin m → ℝ => ∑ i, y i ^ 2) from ?_]
  · rw [← Measure.map_map (by fun_prop) (by fun_prop),
      pi_gaussianReal_map_sumSq_eq_chiSq, projNormSq]
  · ext y
    simp only [Function.comp_apply, mul_pow]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- **Per-pair distortion bound.**  For a fixed nonzero `v`, the probability that the
random projection distorts `‖v‖²` by more than a factor `ε` is at most `2·exp(-mε²/12)`. -/
lemma rowLaw_pair_bound (m d : ℕ) (m_pos : 0 < m) (v : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    (rowLaw m d).real {G | (1 + ε) * ‖v‖ ^ 2 ≤ (1 / (m : ℝ)) * ∑ i, ⟪v, G i⟫_ℝ ^ 2
                          ∨ (1 / (m : ℝ)) * ∑ i, ⟪v, G i⟫_ℝ ^ 2 ≤ (1 - ε) * ‖v‖ ^ 2}
      ≤ 2 * rexp (-(m : ℝ) * ε ^ 2 / 12) := by
  set f : (Fin m → EuclideanSpace ℝ (Fin d)) → ℝ :=
    fun G => (1 / (m : ℝ)) * ∑ i, ⟪v, G i⟫_ℝ ^ 2 with hf
  have hfmeas : Measurable f := by
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i _
    exact ((innerSL ℝ v).continuous.measurable.comp (measurable_pi_apply i)).pow_const 2
  set U : Set ℝ := {y | (1 + ε) * ‖v‖ ^ 2 ≤ y} ∪ {y | y ≤ (1 - ε) * ‖v‖ ^ 2} with hU
  have hUmeas : MeasurableSet U :=
    (measurableSet_le measurable_const measurable_id).union
      (measurableSet_le measurable_id measurable_const)
  have hpre : {G | (1 + ε) * ‖v‖ ^ 2 ≤ f G ∨ f G ≤ (1 - ε) * ‖v‖ ^ 2} = f ⁻¹' U := by
    ext G; simp only [hU, Set.mem_preimage, Set.mem_union, Set.mem_setOf_eq]
  show (rowLaw m d).real {G | (1 + ε) * ‖v‖ ^ 2 ≤ f G ∨ f G ≤ (1 - ε) * ‖v‖ ^ 2}
    ≤ 2 * rexp (-(m : ℝ) * ε ^ 2 / 12)
  rw [hpre, ← map_measureReal_apply hfmeas hUmeas, rowLaw_map_projSq m d v]
  exact singleVectorConcentration m d m_pos v hv ε hε_pos hε_lt

/-- **Johnson–Lindenstrauss lemma.**  For `n` distinct points in `ℝᵈ`, a random Gaussian
projection to `ℝᵐ` (rescaled by `1/√m`) preserves all pairwise squared distances up to a
factor `(1 ± ε)`, except with probability at most `δ`, provided `2n²·exp(-mε²/12) ≤ δ`. -/
theorem johnsonLindenstrauss (n d : ℕ) (m : ℕ) (m_pos : 0 < m)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (hx : Function.Injective x)
    (ε δ : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) (hδ_pos : 0 < δ)
    (hsuff : 2 * (n : ℝ) ^ 2 * rexp (-(m : ℝ) * ε ^ 2 / 12) ≤ δ) :
    (rowLaw m d).real
      {G | ∃ i j, i ≠ j ∧
        ((1 + ε) * ‖x i - x j‖ ^ 2 ≤ (1 / (m : ℝ)) * ∑ k, ⟪x i - x j, G k⟫_ℝ ^ 2
         ∨ (1 / (m : ℝ)) * ∑ k, ⟪x i - x j, G k⟫_ℝ ^ 2 ≤ (1 - ε) * ‖x i - x j‖ ^ 2)}
      ≤ δ := by
  classical
  -- The bad set for a single pair `p = (i, j)`.
  set badPair : Fin n × Fin n → Set (Fin m → EuclideanSpace ℝ (Fin d)) :=
    fun p => {G | (1 + ε) * ‖x p.1 - x p.2‖ ^ 2 ≤ (1 / (m : ℝ)) * ∑ k, ⟪x p.1 - x p.2, G k⟫_ℝ ^ 2
      ∨ (1 / (m : ℝ)) * ∑ k, ⟪x p.1 - x p.2, G k⟫_ℝ ^ 2 ≤ (1 - ε) * ‖x p.1 - x p.2‖ ^ 2}
    with hbadPair
  set S : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 ≠ p.2) with hS
  -- The bad set is contained in the union over distinct pairs.
  have hsub : {G | ∃ i j, i ≠ j ∧
        ((1 + ε) * ‖x i - x j‖ ^ 2 ≤ (1 / (m : ℝ)) * ∑ k, ⟪x i - x j, G k⟫_ℝ ^ 2
         ∨ (1 / (m : ℝ)) * ∑ k, ⟪x i - x j, G k⟫_ℝ ^ 2 ≤ (1 - ε) * ‖x i - x j‖ ^ 2)}
      ⊆ ⋃ p ∈ S, badPair p := by
    intro G hG
    obtain ⟨i, j, hij, hP⟩ := hG
    simp only [Set.mem_iUnion]
    refine ⟨(i, j), ?_, hP⟩
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hij
  -- Bound by the union, then by the sum over pairs.
  calc (rowLaw m d).real {G | ∃ i j, i ≠ j ∧ _}
      ≤ (rowLaw m d).real (⋃ p ∈ S, badPair p) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ p ∈ S, (rowLaw m d).real (badPair p) := measureReal_biUnion_finset_le S _
    _ ≤ ∑ _p ∈ S, 2 * rexp (-(m : ℝ) * ε ^ 2 / 12) := by
        apply Finset.sum_le_sum
        intro p hp
        simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        have hvne : x p.1 - x p.2 ≠ 0 := sub_ne_zero.mpr (fun h => hp (hx h))
        exact rowLaw_pair_bound m d m_pos (x p.1 - x p.2) hvne ε hε_pos hε_lt
    _ = (S.card : ℝ) * (2 * rexp (-(m : ℝ) * ε ^ 2 / 12)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) ^ 2 * (2 * rexp (-(m : ℝ) * ε ^ 2 / 12)) := by
        have hcard : (S.card : ℝ) ≤ (n : ℝ) ^ 2 := by
          have : S.card ≤ n ^ 2 := by
            calc S.card ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
                  Finset.card_le_card (Finset.filter_subset _ _)
              _ = n ^ 2 := by rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]
          exact_mod_cast this
        have hnn : (0 : ℝ) ≤ 2 * rexp (-(m : ℝ) * ε ^ 2 / 12) := by positivity
        exact mul_le_mul_of_nonneg_right hcard hnn
    _ = 2 * (n : ℝ) ^ 2 * rexp (-(m : ℝ) * ε ^ 2 / 12) := by ring
    _ ≤ δ := hsuff

end JL
