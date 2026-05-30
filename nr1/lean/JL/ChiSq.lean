import JL.Basic
import JL.GaussianMGF
import Mathlib.MeasureTheory.Integral.Pi

/-!
# JL §3 — Chi-squared MGF

`mgf id (χ²_m) t = (1 - 2t)^(-m/2)` for `t < 1/2`.

`χ²_m = ‖g‖²` with `g ∼ N(0, I_m)`.  Writing `stdGaussian` as the pushforward of the
product measure `⊗ N(0,1)` under `toLp 2`, the squared norm becomes `∑ xᵢ²`, so the
exponential factorises into a product of one-dimensional MGFs, each `(1-2t)^(-1/2)`
(`mgf_sqNorm_stdNormal`).  Their product is `(1-2t)^(-m/2)`.
-/

open MeasureTheory ProbabilityTheory Real Set BigOperators

namespace JL

/-- `‖toLp 2 v‖² = ∑ i, vᵢ²`. -/
lemma norm_toLp_sq (m : ℕ) (v : Fin m → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin m))‖ ^ 2 = ∑ i, v i ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]

/-- **MGF of the chi-squared distribution:** `mgf id (χ²_m) t = (1-2t)^(-m/2)` for `t < 1/2`. -/
theorem chiSq_mgf (m : ℕ) (t : ℝ) (ht : t < 1 / 2) :
    mgf id (chiSq m) t = (1 - 2 * t) ^ (-(m : ℝ) / 2) := by
  have h_pos : 0 < 1 - 2 * t := by linarith
  -- mgf id μ t = ∫ exp(t·x) dμ
  simp only [mgf, id_eq]
  -- χ²_m = stdGaussian.map ‖·‖²  →  ∫ exp(t·‖x‖²) dstdGaussian
  rw [chiSq, integral_map (by fun_prop) (by fun_prop)]
  -- stdGaussian = (⊗ N(0,1)).map (toLp 2)  →  ∫ exp(t·‖toLp 2 v‖²) d(⊗N(0,1))
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [norm_toLp_sq, Finset.mul_sum, Real.exp_sum]
  -- factorise the product integral
  rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin m) (y : ℝ) => rexp (t * y ^ 2))]
  -- each factor is (1-2t)^(-1/2)
  simp_rw [mgf_sqNorm_stdNormal t ht]
  -- ∏_{i<m} (1-2t)^(-1/2) = (1-2t)^(-m/2)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.rpow_natCast ((1 - 2 * t) ^ (-(1/2) : ℝ)) m, ← Real.rpow_mul h_pos.le]
  congr 1
  push_cast
  ring

end JL
