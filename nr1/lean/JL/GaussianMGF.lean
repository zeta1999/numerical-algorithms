import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# JL §2 — MGF of a squared standard normal

`E[exp(t·Z²)] = (1 - 2t)^(-1/2)` for `t < 1/2`, where `Z ∼ N(0,1)`.

This is the one-dimensional building block; the chi-squared MGF (`§3`) is its `m`-fold
product.  The proof: complete the square inside the Gaussian integral and apply the
classical `∫ exp(-b x²) dx = √(π/b)`.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace JL

/-- `gaussianPDFReal 0 1 x = (√(2π))⁻¹ · exp(-x²/2)`. -/
lemma gaussianPDFReal_std (x : ℝ) :
    gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]

/-- **MGF of `Z²` for `Z ∼ N(0,1)`:** `∫ exp(t·x²) dN(0,1) = (1-2t)^(-1/2)` for `t < 1/2`. -/
theorem mgf_sqNorm_stdNormal (t : ℝ) (ht : t < 1 / 2) :
    ∫ x : ℝ, rexp (t * x ^ 2) ∂gaussianReal 0 1 = (1 - 2 * t) ^ (-(1/2) : ℝ) := by
  have h_pos : 0 < 1 - 2 * t := by linarith
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have ht' : (1:ℝ) / 2 - t ≠ 0 := by linarith
  -- Pass to the density and combine the two exponentials.
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero)]
  simp only [gaussianPDFReal_std, smul_eq_mul]
  have hcomb : ∀ x : ℝ,
      (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) * rexp (t * x ^ 2)
        = (√(2 * π))⁻¹ * rexp (-(1 / 2 - t) * x ^ 2) := by
    intro x
    rw [mul_assoc, ← Real.exp_add, show -x ^ 2 / 2 + t * x ^ 2 = -(1 / 2 - t) * x ^ 2 by ring]
  simp_rw [hcomb]
  rw [integral_const_mul, integral_gaussian]
  -- Final algebra: (√(2π))⁻¹ · √(π/(1/2-t)) = (1-2t)^(-1/2).
  -- Normalise both sides to `√((1-2t)⁻¹)`.
  have key : (√(2 * π))⁻¹ * √(π / (1 / 2 - t)) = √((1 - 2 * t)⁻¹) := by
    rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  rw [key, Real.rpow_neg h_pos.le, Real.sqrt_inv, Real.sqrt_eq_rpow]

end JL
