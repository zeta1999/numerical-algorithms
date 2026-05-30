import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Basic

/-!
# JL — Basic definitions

Shared opens and the chi-squared distribution `χ²_m`, defined as the law of `‖g‖²`
for a standard Gaussian vector `g ∼ N(0, I_m)`.
-/

open MeasureTheory ProbabilityTheory NNReal Real Set
open scoped RealInnerProductSpace

namespace JL

/-- The chi-squared distribution with `m` degrees of freedom:
the law of `‖g‖²` where `g ∼ N(0, I_m)`. -/
noncomputable def chiSq (m : ℕ) : Measure ℝ :=
  (stdGaussian (EuclideanSpace ℝ (Fin m))).map (fun x => ‖x‖ ^ 2)

/-- `x ↦ ‖x‖²` is measurable. -/
lemma measurable_normSq {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [OpensMeasurableSpace E] : Measurable (fun x : E => ‖x‖ ^ 2) :=
  measurable_norm.pow_const 2

/-- Chi-squared is a probability measure. -/
instance isProbMeasure_chiSq (m : ℕ) : IsProbabilityMeasure (chiSq m) := by
  rw [chiSq]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

end JL
