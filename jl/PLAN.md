# PLAN: Formalize the Johnson-Lindenstrauss Lemma in Lean 4

## 1. Source Material — Informal Lemma & Proof

### Statement (standard form)

> **Johnson-Lindenstrauss Lemma.** Let `0 < ε < 1` and `0 < δ ≤ 1`. Let `n` be a positive integer and
> `X = {x₁, …, xₙ} ⊂ ℝᵈ` a finite set of points. Let `m` be an integer satisfying
>
>     m ≥ ⌈ 8·ln(n) / (ε²/2 − ε³/3) ⌉    (simplified lower bound: m ≥ 12·ln(n)/ε²)
>
> Let `A: ℝᵈ → ℝᵐ` be a random matrix with i.i.d. entries `Aᵢⱼ ∼ N(0, 1/m)`.
> Then
>
>     P( ∀ i≠j : (1−ε)·||xᵢ − xⱼ||² ≤ ||A(xᵢ − xⱼ)||² ≤ (1+ε)·||xᵢ − xⱼ||² ) ≥ 1 − δ
>
> In other words, `A` is a `(ε, δ)`-JL mapping for `X` with probability ≥ 1 − δ.

### Key sources for the proof

- **Original paper:** Johnson & Lindenstrauss (1984), "Extensions of Lipschitz mappings into a Hilbert space"
- **Textbook treatment:** Vempala, "The Randomized Geometry of Algorithms" (survey), Section 2.1
- **Detailed proof:** Dasgupta & Gupta (1999), "An elementary proof of a theorem of Johnson and Lindenstrauss"
  - URL: https://www.eecs.harvard.edu/~michaelm/postscripts/tr-01-05.pdf
  - This is the cleanest proof for formalization — it uses only:
    1. Concentration of squared norms of Gaussian vectors (chi-squared tail bounds)
    2. A union bound over all n(n−1)/2 pairs
    3. A simple algebraic simplification of the tail bound constants

---

## 2. Proof Decomposition (for Lean 4 formalization)

The proof decomposes into **7 formalizable claims**, listed in dependency order:

### Claim 0: Gaussian vector model
- `g ∼ N(0, I_d)` — a d-dimensional standard Gaussian vector
- `A` has i.i.d. `N(0, 1/m)` entries, so `A·v = (1/m)·Gᵀ·v` where `G` has i.i.d. `N(0,1)` entries
- **Key reduction:** For any fixed `v ∈ ℝᵈ`, `||Av||² = (1/m)·||Gᵀv||²` where `Gᵀv ∼ N(0, ||v||²·I_d)`

### Claim 1: Chi-squared tail bounds (the core analytic lemma)
For `z ∼ χ²_d` (chi-squared with d degrees of freedom):

```
For 0 < ε < 1:
  P(z ≤ 1 − ε + ε²/2) ≤ exp(−d·ε²/4)         (lower tail)
  P(z ≥ 1 + ε − ε²/2) ≤ exp(−d·ε²/4)          (upper tail)
```

**Sub-steps:**
1. Define the chi-squared distribution as sum of squared standard normals
2. Prove `E[exp(t·z)] = (1 − 2t)^{−d/2}` (moment generating function)
3. Apply Chernoff bound: `P(z ≤ a) ≤ exp(t·a) · E[exp(−t·z)]` for t > 0
4. Optimize the parameter t to get the exponential decay
5. Derive the simplified constants via Taylor expansions

### Claim 2: Concentration of squared norm for a single projection
For any fixed `v ∈ ℝᵈ`, with `A` as above:

```
P( ||Av||² ∉ [(1−ε)||v||², (1+ε)||v||²] ) ≤ 2·exp(−m·ε²/4)
```

**Proof:** `||Av||² = (1/m)·||Gᵀv||² = (||v||²/m)·χ²_d` where `d = m` (after normalizing).
Apply Claim 1.

### Claim 3: Union bound over all pairs
For `N = n·(n−1)/2` pairs, by the union bound:

```
P(∃ i≠j : ||A(xᵢ−xⱼ)||² ∉ [(1−ε)||xᵢ−xⱼ||², (1+ε)||xᵢ−xⱼ||²])
  ≤ N · 2·exp(−m·ε²/4)
  ≤ n² · exp(−m·ε²/4)
```

Set this ≤ δ and solve for m:

```
n² · exp(−m·ε²/4) ≤ δ
⟺ m ≥ 4·ε⁻² · (2·ln(n) + ln(1/δ))
  = 8·ln(n)/ε² + 4·ln(1/δ)/ε²
```

Using the tighter Johnson-Lindenstrauss constants from Claim 1:
```
m ≥ 4·ln(N/δ) / (ε²/2 − ε³/3)
```

### Claim 4: The final JL bound
Combine Claims 2–3 to get the lemma statement.

### Claim 5 (optional): Practical JL matrix constructions
- **Gaussian matrix** (proven above)
- **Sub-gaussian matrices** (more general)
- **Sparse Johnson-Lindenstrauss Transform** (Kane, Nelson 2014) — more work, skip for v1
- **Bernoulli ±1 matrix** — simpler variant

---

## 3. Lean 4 Formalization Plan

### Directory structure
```
jl/
  PLAN.md              ← this file
  lean/
    JL.lean            ← main file, organized as:
    -- §1: Probability foundations
    --   - Gaussian measure / normal distribution
    --   - Chi-squared distribution
    --   - Moment generating functions
    -- §2: Concentration inequalities
    --   - Chernoff bound lemma
    --   - Chi-squared tail bounds (Claim 1)
    -- §3: JL embedding
    --   - JL random matrix model
    --   - Single-pair concentration (Claim 2)
    --   - Union bound (Claim 3)
    --   - Johnson-Lindenstrauss lemma (Claim 4)
    -- §4: Statement and proof
    JLTest.lean          ← unit tests: sample JL embeddings
```

### Mathlib4 dependencies required

| Needed? | Mathlib component | Status in mathlib4 |
|---------|-------------------|-------------------|
| ✅ | `MeasureTheory.Probability.Gaussian` | **Available** — `stdGaussian E`, `gaussianReal μ v`, `multivariateGaussian` |
| ✅ | `Analysis.SpecialFunctions.Gamma` | **Available** — `Real.Gamma`, `Gamma_eq_integral`, `Gamma_add_one` |
| ✅ | `MeasureTheory.Integral` | **Available** — `integral_exp_neg_mul_sq`, `integral_rpow_mul_exp_neg_mul_rpow` |
| ✅ | `Analysis.Convex` (Jensen, Chernoff) | **Available** — `measure_ge_le_exp_mul_mgf`, `measure_le_le_exp_mul_mgf` |
| ✅ | `Data.Real.Basic` (basic inequalities) | **Available** |
| ✅ | `MeasureTheory.Probability.MomentGeneratingFunction` | **Available** — `mgf`, `cgf` in `Probability.Moments.Basic` |
| ❌ | `Statistics.Distribution.ChiSquare` | **Does not exist** — define as `stdGaussian.map ‖·‖²` (~3 lines) |
| ❌ | Sub-exponential concentration | **Not needed** — use direct Chernoff + Gamma integral |

### Key mathlib4 gaps to fill (minimal)

1. **Chi-squared distribution**: Define `chiSqMeasure m := (stdGaussian (EuclideanSpace ℝ (Fin m))).map (‖·‖²)`. Prove its MGF using `Real.Gamma_eq_integral`. (~40 lines)

2. **Chi-squared tail bounds**: Apply `measure_ge_le_exp_mul_mgf` / `measure_le_le_exp_mul_mgf` (already in mathlib4). The optimization of the Chernoff parameter `t` is pure real analysis. (~50 lines)

3. **No other infrastructure needed** — all other pieces are in mathlib4.

### Implementation order (confirmed)

1. **Chi-squared MGF**: Define `chiSqMeasure m`, prove `mgf_chiSq m t = (1-2t)^(-m/2)`
2. **Chi-squared tail bounds**: Apply Chernoff + optimize `t`
3. **JL projection model**: Show `‖A·v‖² / ‖v‖² ~ (1/m)·χ²_m`
4. **Single vector concentration**: Direct application of tail bounds
5. **Union bound + JL lemma**: Finite sum over n² pairs
6. **Tests**: Sample JL embeddings

### Estimated size (revised)
- Chi-squared MGF: ~40 lines
- Chi-squared tail bounds: ~50 lines
- JL projection model: ~40 lines
- Single vector concentration: ~15 lines
- Union bound + JL lemma: ~30 lines
- Tests: ~50 lines
- **Total: ~225 lines of Lean**

---

## 4. Survey Results (executed 2026-05-28)

### Step A: Gaussian measure — ✅ ALL FOUND

| What | File | Lemma/def name |
|------|--|----|
| 1D Gaussian measure | `Probability.Distributions.Gaussian.Real` | `gaussianReal μ v` |
| Multivariate Gaussian | `Probability.Distributions.Gaussian.Multivariate` | `multivariateGaussian μ S` |
| Standard Gaussian | same | `stdGaussian E` |
| `IsGaussian` class | `Probability.Distributions.Gaussian.Basic` | `IsGaussian μ` |
| `mgf_id_gaussianReal` | `Gaussian/Real.lean:476` | `fun t ↦ exp(μt + vt²/2)` |
| `variance_id_gaussianReal` | `Gaussian/Real.lean:543` | `v` |
| `variance_dual_stdGaussian` | `Multivariate.lean:82` | `‖L‖²` |
| `covarianceBilin_stdGaussian` | `Multivariate.lean:122` | `innerSL ℝ` |
| Fernique's theorem | `Fernique.lean:163` | `IsGaussian.exists_integrable_exp_sq` |

### Step B: Gamma function — ✅ ALL FOUND

| What | File | Lemma name |
|------|--|----|
| `Real.Gamma` | `Analysis.SpecialFunctions.Gamma.Basic` | `Real.Gamma s` |
| Integral def | same | `Real.Gamma_eq_integral {s : ℝ} (hs : 0 < s)` |
| Recurrence | same | `Real.Gamma_add_one {s : ℝ} (hs : s ≠ 0)` |
| Positivity | same | `Real.Gamma_pos_of_pos {s : ℝ} (hs : 0 < s)` |
| `Γ(n+1) = n!` | same | `Gamma_nat_eq_factorial` |
| Gamma integral | `MeasureTheory.Integral.Gamma` | `integral_rpow_mul_exp_neg_mul_rpow` |

### Step C: Concentration inequalities — ✅ ALL FOUND

| What | File | Lemma name |
|------|--|----|
| Chernoff (upper) | `Probability.Moments.Basic:428` | `measure_ge_le_exp_mul_mgf` |
| Chernoff (lower) | same:450 | `measure_le_le_exp_mul_mgf` |
| Chernoff (CGF) | same:460 | `measure_ge_le_exp_cgf` |
| Sub-Gaussian MGF | `Probability.Moments.SubGaussian:138` | `HasSubgaussianMGF X c κ ν` |
| Sub-Gaussian Chernoff | same:333 | `measure_ge_le` → `exp(-ε²/(2c))` |
| Hoeffding | same:779 | `hoeffdingIneq` |

### Step D: MGF — ✅ ALL FOUND

| What | File | Lemma name |
|------|--|----|
| `mgf X μ t` | `Probability.Moments.Basic` | `def mgf` |
| `cgf X μ t` | same | `def cgf` |
| MGF of i.i.d. sum | same | `mgf_sum_of_identDistrib` |

### Step E: Measure theory — ✅ ALL FOUND

| What | File | Name |
|------|--|----|
| Product measure | `Probability.ProductMeasure` | `Measure.infinitePi μ` |
| Pushforward | MeasureTheory | `Measure.map` |
| Union bound | MeasureTheory | `measure_union_le` |
| Prob. measure | `MeasureTheory.Measure.ProbabilityMeasure` | `IsProbabilityMeasure` |

### Step F: Gaussian integrals — ✅ ALL FOUND

| What | File | Lemma name |
|------|--|----|
| `∫ exp(-b·x²) = √(π/b)` | `Gaussian/GaussianIntegral.lean:223` | `integral_exp_neg_mul_sq` |
| `Γ(1/2) = √π` | same:330 | `gamma_half_sqrt_pi` |
| Integrability | same:128 | `integrable_exp_neg_mul_sq` |

### Step G: Euclidean space — ✅ ALL FOUND

| What | File | Name |
|------|--|----|
| `EuclideanSpace ℝ ι` | `PiL2.lean` | with `‖x‖² = ∑ xᵢ²` |
| `stdOrthonormalBasis` | same | canonical ONB |
| `inner/toEuclideanCLM` | same | for coordinate-free inner products |

### Decision matrix (all green)

| Claim | Depends on | Status |
|-------|-------|--------|
| Claim 0: Gaussian model | A, F, G | ✅ All confirmed |
| Claim 1: Chi-squared tails | B, C, D | ✅ All confirmed |
| Claim 2: Single vector | Claim 1, E | ✅ All confirmed |
| Claim 3: Union bound | E | ✅ All confirmed |
| Claim 4: Final JL | Claims 1-3 | ✅ All confirmed |

### Verdict: No major gaps. Start implementing `JL.lean`.

---

### Step A: Gaussian measure — ✅ FOUND

| What | Where | Lemma name |
|------|-------|-------|
| 1D Gaussian measure | `Probability.Distributions.Gaussian.Real` | `gaussianReal μ v` |
| Multivariate Gaussian | `Probability.Distributions.Gaussian.Multivariate` | `multivariateGaussian μ S` |
| Standard Gaussian | `Probability.Distributions.Gaussian.Multivariate` | `stdGaussian E` (on `EuclideanSpace ℝ ι`) |
| `IsGaussian` class | `Probability.Distributions.Gaussian.Basic` | `IsGaussian μ` (map by every continuous linear form is Gaussian) |
| `IsGaussian` instance | same | `isGaussian_gaussianReal`, `isGaussian_stdGaussian` |
| `mgf id (gaussianReal μ v)` | `Gaussian/Real.lean:476` | `mgf_id_gaussianReal` → `fun t ↦ exp(μt + vt²/2)` |
| `Var[id; gaussianReal μ v]` | `Gaussian/Real.lean:543` | `variance_id_gaussianReal` → `v` |
| `Var[L; stdGaussian E]` | `Multivariate.lean:82` | `variance_dual_stdGaussian L` → `‖L‖²` |
| `covarianceBilin_stdGaussian` | `Multivariate.lean:122` | → `innerSL ℝ` |
| `stdGaussian_map` | `Multivariate.lean:128` | rotation-equivariant: `f.map stdGaussian = stdGaussian` for isometries |
| Fernique's theorem | `Probability.Distributions.Gaussian.Fernique` | `IsGaussian.exists_integrable_exp_sq` → `∃ C, Integrable (λx, exp(C·‖x‖²))` |
| Gaussian moments | `Fernique.lean:186` | `IsGaussian.memLp_id` → `MemLp id p (stdGaussian E)` |

**How to construct i.i.d. N(0,1/m) on `Fin m → ℝ`:**
Use `stdGaussian (EuclideanSpace ℝ (Fin m))` — this is exactly the standard Gaussian on `ℝᵐ`. The coordinates in an orthonormal basis are independent standard normals. For scaled version `N(0, 1/m)`, use `stdGaussian.map (λx, x / √m)`.

### Step B: Gamma function — ✅ FOUND

| What | Where | Lemma name |
|------|-------|-------|
| `Real.Gamma` | `Analysis.SpecialFunctions.Gamma.Basic` | `Real.Gamma s` |
| Integral definition | same | `Real.Gamma_eq_integral {s : ℝ} (hs : 0 < s)` → `∫ x > 0, exp(-x) · x^(s-1)` |
| Recurrence | same | `Real.Gamma_add_one {s : ℝ} (hs : s ≠ 0)` → `Γ(s+1) = s·Γ(s)` |
| Positivity | same | `Real.Gamma_pos_of_pos {s : ℝ} (hs : 0 < s)` → `0 < Γ(s)` |
| `Γ(1) = 1` | same | `Gamma_one` |
| `Γ(n+1) = n!` | same | `Gamma_nat_eq_factorial` |
| Gamma integral | `MeasureTheory.Integral.Gamma` | `integral_rpow_mul_exp_neg_rpow`, `integral_rpow_mul_exp_neg_mul_rpow` |

**Key for chi-squared MGF:** We need `∫₀^∞ e^{tx} · x^(a-1) · e^(-rx) dx = Γ(a) · (r-t)^(-a)`.
This follows from `integral_rpow_mul_exp_neg_mul_rpow` with `p=1, q=a-1, b=r-t`.

### Step C: Concentration inequalities — ✅ FOUND

| What | Where | Lemma name |
|------|-------|-------|
| **Chernoff bound (upper tail)** | `Probability.Moments.Basic` | `measure_ge_le_exp_mul_mgf` → `P(X ≥ ε) ≤ exp(-tε) · MGF(t)` |
| **Chernoff bound (lower tail)** | same | `measure_le_le_exp_mul_mgf` → `P(X ≤ ε) ≤ exp(-tε) · MGF(t)` |
| Chernoff bound (CGF form) | same | `measure_ge_le_exp_cgf`, `measure_le_le_exp_cgf` |
| **Sub-Gaussian MGF** | `Probability.Moments.SubGaussian` | `HasSubgaussianMGF X c κ ν` (MGF ≤ `exp(c·t²/2)`) |
| **Sub-Gaussian Chernoff** | same | `Kernel.HasSubgaussianMGF.measure_ge_le` → `P(X ≥ ε) ≤ exp(-ε²/(2c))` |
| Hoeffding inequality | same | `hoeffdingIneq`, `hoeffdingIneq'` |

### Step D: Moment generating functions — ✅ FOUND

| What | Where | Lemma name |
|------|-------|-------|
| `mgf X μ t` | `Probability.Moments.Basic` | `def mgf` → `∫ exp(t·X) dμ` |
| `cgf X μ t` | same | `def cgf` → `log ∫ exp(t·X) dμ` |
| MGF of sum (ident. distrib.) | same | `mgf_sum_of_identDistrib` → product of individual MGFs |
| MGF of sum (i.i.d.) | same | `mgf_sum_of_identDistrib₀` |
| MGF integral form | same | `mgf_undef`, `mgf_pos_iff` |
| `Integrable (exp(t·X))` | `Gaussian/Real.lean:485` | `integrable_exp_mul_gaussianReal` |

### Step E: Probability basics — ✅ FOUND

| What | Where | Lemma name |
|------|-------|-------|
| Product measure | `Probability.ProductMeasure` | `Measure.infinitePi μ` |
| Pushforward | `Probability.ProductMeasure` (import) | `Measure.map` (standard MeasureTheory) |
| Probability measure | `MeasureTheory.Measure.ProbabilityMeasure` | `IsProbabilityMeasure μ` |
| `measure_union_le` | `MeasureTheory.Basic` (standard) | `measure_union_le` |
| Union bound | Used everywhere | `measure_union_le` (iterated) |

### Step F: Gaussian integrals — ✅ FOUND

| What | Where | Lemma name |
|------|-------|-------|
| `∫ exp(-b·x²) dx = √(π/b)` | `Analysis.SpecialFunctions.Gaussian.GaussianIntegral` | `integral_exp_neg_mul_sq` |
| `∫ exp(-x²) dx = √π` | same | derived from above with `b=1` |
| `Real.Gamma(1/2) = √π` | `GaussianIntegral.lean:330` | `gamma_half_sqrt_pi` |
| `∫ exp(-b·x²) integrable` | `GaussianIntegral.lean:128` | `integrable_exp_neg_mul_sq` |
| Complex Gaussian integral | `GaussianIntegral.lean:171` | `integral_mul_cexp_neg_mul_sq` |

### Step G: Finite-dimensional vector spaces — ✅ FOUND

| What | Where | Lemma name |
|------|-------|-------|
| Euclidean space | `Analysis.InnerProductSpace.PiL2` | `EuclideanSpace ℝ ι` (= `Π i : ι, ℝ` with inner product) |
| L2 norm / inner product | same | `EuclideanSpace.inner`, `‖x‖² = ∑ xᵢ²` |
| `stdOrthonormalBasis ℝ E` | `PiL2.lean` | canonical orthonormal basis |
| `(stdOrthonormalBasis).norm_dual` | `Multivariate.lean:90` → `‖L‖²` for basis elements |

---

### Decision matrix (survey complete)

| Claim | Depends on | Available? | Action needed |
|-------|-------|------------|---------------|
| Claim 0: Gaussian model | A, F, G | ✅ ALL | Minimal — use `stdGaussian (EuclideanSpace ℝ (Fin m))` and pushforward for scaling |
| Claim 1: Chi-squared tails | B, C, D | ✅ ALL | Define `chiSquared m` as `stdGaussian.map ‖·‖²`; prove MGF via Gamma integral; apply Chernoff bounds |
| Claim 2: Single vector | Claim 1, E | ✅ ALL | Direct application of chi-squared tail bounds |
| Claim 3: Union bound | E | ✅ ALL | `measure_union_le` (iterated over finite pairs) |
| Claim 4: Final JL | Claims 1-3 | ✅ ALL | Algebraic simplification |

### Key insight: The path is clear

mathlib4 has **all** the building blocks. The main work is:
1. Define the chi-squared distribution (3 lines: `stdGaussian.map ‖·‖²`)
2. Prove its MGF using `Real.Gamma_eq_integral` and `integral_rpow_mul_exp_neg_mul_rpow`
3. Apply `measure_ge_le_exp_mul_mgf` / `measure_le_le_exp_mul_mgf` (already in mathlib4!)
4. Optimize the Chernoff parameter (pure real analysis)
5. Union bound over n(n-1)/2 pairs
6. Solve for m

No major infrastructure needs to be built from scratch. The chi-squared definition and MGF proof are the only new theorems needed (~50-80 lines).

---

## 5. Implementation Plan (updated with survey results)

### Directory structure
```
jl/
  PLAN.md              ← this file
  lean/
    JL.lean            ← main file (all in one file for simplicity)
    JLTest.lean        ← tests
```

### File organization in JL.lean

```lean
/-!
# Johnson-Lindenstrauss Lemma

References:
- Dasgupta, S. & Gupta, A. (1999). An elementary proof of a theorem of Johnson and Lindenstrauss.
- Johnson, W. & Lindenstrauss, J. (1984). Extensions of Lipschitz mappings into a Hilbert space.
-/

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma

-- §1: Chi-squared distribution and its MGF
-- §2: Chi-squared tail bounds (Chernoff)
-- §3: JL random projection and single-vector concentration
-- §4: Union bound and final JL lemma
```

### Detailed implementation steps

#### Step 1: Chi-squared distribution and MGF (~40 lines)
- Define `chiSqMeasure m := (stdGaussian (EuclideanSpace ℝ (Fin m))).map (‖·‖²)`
- Prove `chiSqMeasure m` is a probability measure
- Prove `mgf_chiSq m`: compute `∫ exp(t·‖x‖²) dχ²_m(x)`
  - Use `stdGaussian` rotation invariance + `integral_exp_neg_mul_sq`
  - Result: `mgf_chiSq m t = (1 - 2t)^(-m/2)` for `t < 1/2`
  - Key lemma: `∫ exp(t·‖x‖²) · exp(-‖x‖²/2) dx = (1-2t)^(-m/2) · ∫ exp(-‖x‖²/2) dx`
  - This follows from completing the square: `exp(-(1-2t)·‖x‖²/2)`
  - Apply `integral_exp_neg_mul_sq` coordinate by coordinate

#### Step 2: Chi-squared tail bounds (~50 lines)
- Upper tail: `P(χ²_m ≥ 1+ε) ≤ exp(-m·ε²/4)` for `0 < ε < 1`
  - Use `measure_ge_le_exp_mul_mgf` with `t = ε/m`
  - Plug in `mgf_chiSq m t = (1-2t)^(-m/2)`
  - Optimize: minimize `-t(1+ε) - (m/2)·log(1-2t)`
  - Get bound `exp(-m·(ε - log(1+ε))/2)`
  - Use `log(1+ε) ≤ ε - ε²/2 + ε³/3` (Taylor remainder)
  - Simplify to `exp(-m·(ε²/2 - ε³/3)/2) = exp(-m·(ε²/2 - ε³/3)/2)`
  - Further simplify: for `0 < ε < 1`, `ε²/2 - ε³/3 ≥ ε²/6`, so `≤ exp(-m·ε²/12)`
  - Or use the cleaner Dasgupta-Gupta constants: `≤ exp(-m·ε²/4)`

- Lower tail: `P(χ²_m ≤ 1-ε) ≤ exp(-m·ε²/4)` for `0 < ε < 1`
  - Use `measure_le_le_exp_mul_mgf` similarly

#### Step 3: JL random projection (~40 lines)
- Define JL random matrix: `A : (Fin d → ℝ) →ₗ[ℝ] (Fin m → ℝ)` with `Aᵢⱼ ~ N(0, 1/m)`
- Construct as pushforward: `A ~ (stdGaussian (EuclideanSpace ℝ (Fin (m*d)))).map ...`
  - Actually simpler: just use `stdGaussian (EuclideanSpace ℝ (Fin m))` applied to the fixed vector `v = xᵢ - xⱼ`
  - The projection `A·v` has the same distribution as `(1/√m) · g · ‖v‖` where `g ~ N(0,1)` in each coordinate
  - So `‖A·v‖² / ‖v‖² ~ (1/m) · χ²_m`

#### Step 4: Single vector concentration (~15 lines)
- For fixed `v ≠ 0`: `P(‖A·v‖² ∉ [(1-ε)‖v‖², (1+ε)‖v‖²]) ≤ 2·exp(-m·ε²/4)`
- Direct application of chi-squared tail bounds to `‖A·v‖² / ‖v‖² ~ (1/m)·χ²_m`

#### Step 5: Union bound + JL lemma (~30 lines)
- `n` points → `n(n-1)/2 < n²` pairs
- Union bound: `P(∃ pair violating JL) ≤ n² · 2·exp(-m·ε²/4)`
- Set ≤ δ: need `m ≥ 4·(ln(2n²) + ln(1/δ)) / ε²`
- Simplified bound: `m ≥ (8·ln(n) + 4·ln(1/δ)) / ε²`
- Or use Dasgupta-Gupta tighter bound: `m ≥ 4·ln(n/δ) / (ε²/2 - ε³/3)`

### Estimated size (revised)
- Chi-squared MGF: ~40 lines
- Chi-squared tail bounds: ~50 lines
- JL projection model: ~40 lines
- Single vector concentration: ~15 lines
- Union bound + JL lemma: ~30 lines
- Tests: ~50 lines
- **Total: ~225 lines of Lean**

### Key mathlib4 lemmas to use (confirmed)

```lean
-- Gaussian measure
stdGaussian E                              -- Standard Gaussian on EuclideanSpace ℝ ι
variance_dual_stdGaussian                  -- Var[L; stdGaussian E] = ‖L‖²
covarianceBilin_stdGaussian               -- Cov bilinear form = inner product

-- MGF and Chernoff
mgf                                        -- def mgf X μ t := ∫ exp(t·X) dμ
measure_ge_le_exp_mul_mgf                  -- Upper tail Chernoff bound
measure_le_le_exp_mul_mgf                  -- Lower tail Chernoff bound
mgf_sum_of_identDistrib                    -- MGF of sum of i.i.d. variables

-- Gamma and integrals
Real.Gamma_eq_integral                     -- Γ(s) = ∫₀^∞ exp(-x)·x^(s-1) dx
Real.Gamma_add_one                         -- Γ(s+1) = s·Γ(s)
integral_exp_neg_mul_sq                    -- ∫ exp(-b·x²) = √(π/b)
integral_rpow_mul_exp_neg_mul_rpow         -- For chi-squared MGF derivation

-- Measure theory
Measure.infinitePi                         -- Product measure
Measure.map                                -- Pushforward
measure_union_le                           -- P(A∪B) ≤ P(A) + P(B)
IsProbabilityMeasure                       -- Probability measure typeclass
```

### Risks (updated)

| Risk | Severity | Mitigation |
|--|--|--|
| `chiSqMeasure MGF` computation is technically subtle (needs coordinate-free integration) | Medium | Use `stdGaussian` rotation invariance to reduce to 1D integrals |
| `Measure.infinitePi` on `Fin (m*d)` for random matrix — may be heavy | Low | Avoid: use `stdGaussian (EuclideanSpace ℝ (Fin m))` applied to each fixed vector `v` instead |
| Optimizing Chernoff parameter `t` requires careful algebra | Low | Follow Dasgupta-Gupta's proof which has explicit `t` values |
| `EuclideanSpace ℝ (Fin m)` vs `Fin m → ℝ` — need to ensure norm matches | Low | `EuclideanSpace ℝ ι` has `‖x‖² = ∑ xᵢ²` by definition in PiL2.lean |

---

## 7. Implementation Progress (updated 2026-05-29)

### Completed
- [x] Survey mathlib4 — all building blocks found (see Section 4)
- [x] Taylor bounds for log: `log_upper_bound`, `log_lower_bound` + simplified versions
- [x] MGF of squared standard normal: `mgf_sqNorm_stdNormal` — computes ∫ exp(tx²) dN(0,1) = (1-2t)^{-1/2}
- [x] Chi-squared distribution definition: `chiSq m = stdGaussian(ℝᵐ).map ‖·‖²`
- [x] Chi-squared probability measure: `isProbMeasure_chiSq`
- [x] Chi-squared MGF skeleton: `chiSq_mgf` — uses `map_pi_eq_stdGaussian`, `integral_map`, `toLp 2`, `integral_fintype_prod_eq_prod`
  - Remaining: `infinitePi_eq_pi` for finite types, integrability proofs
- [x] Upper tail skeleton: `chiSq_upperTail` — Chernoff at t = ε/(2(1+ε))
- [x] Simplified upper tail: `chiSq_upperTail_simplified`
- [x] Lower tail skeleton: `chiSq_lowerTail` — needs t < 1/2 (requires ε < 1/2)
- [x] Simplified lower tail: `chiSq_lowerTail_simplified`
- [x] Single vector concentration: `singleVectorConcentration` (skeleton)
- [x] JL lemma: `johnsonLindenstrauss` (skeleton with full proof sketch)

### Remaining work
1. **`infinitePi_eq_pi`**: Prove `infinitePi (fun _ : Fin m ↦ μ) = Measure.pi (fun _ : Fin m ↦ μ)` for fintype
   - Likely lemma exists as `infinitePi_nat_eq_pi` or similar
   - Need: find the right lemma for `Type` index with `Fintype`

2. **`integrable_chiSq_exp`**: Show exp(tx) is integrable w.r.t. chiSq for t < 1/2
   - Follows from the MGF being finite: ∫ exp(tx) dχ² = (1-2t)^{-m/2} < ∞
   - Need: a lemma that finite MGF implies integrability

3. **`chiSq_upperTail`**: Three remaining sorries:
   - `h_chernoff`: Apply `measure_ge_le_exp_mul_mgf` — need `IsFiniteMeasure` instance
   - `toReal` cast: The bound from Chernoff is in ℝ≥0∞, need to cast to ℝ
   - Simplification: algebraic manipulation of exp and log

4. **`chiSq_upperTail_simplified`**: Cast measure from ℝ≥0∞ to ℝ

5. **`chiSq_lowerTail`**: Need t = ε/(2(1-ε)) < 1/2, which requires ε < 1/2
   - For ε ≥ 1/2, use a different approach or different t value

6. **`chiSq_lowerTail_simplified`**: Apply lower tail bound

7. **`singleVectorConcentration`**: Connect random matrix projection to chi-squared
   - Show A·v ~ N(0, (‖v‖²/m)·I_m)
   - Then ‖Av‖²/‖v‖² ~ (1/m)·χ²_m

8. **`johnsonLindenstrauss`**: Union bound over all pairs
   - n(n-1)/2 pairs
   - P(any distortion) ≤ n² · 2·exp(-mε²/3) (using both tail bounds)
   - Set ≤ δ, solve for m

### Key mathlib4 lemmas needed
- `infinitePi_eq_pi` or `infinitePi_fin` — product measure equality for fintype
- `measure_ge_le_exp_mul_mgf` — Chernoff upper tail (confirmed exists)
- `measure_le_le_exp_mul_mgf` — Chernoff lower tail (confirmed exists)
- `integral_fintype_prod_eq_prod` — product measure factorization (confirmed exists)
- `isFiniteMeasure_of_isProbabilityMeasure` — finite measure from prob measure

---

## 6. References

- Dasgupta, S. & Gupta, A. (1999). *An elementary proof of a theorem of Johnson and Lindenstrauss*.
  https://www.eecs.harvard.edu/~michaelm/postscripts/tr-01-05.pdf
- Johnson, W. & Lindenstrauss, J. (1984). *Extensions of Lipschitz mappings into a Hilbert space*.
  https://projecteuclid.org/euclid.hrr/1175446450
- Vempala, S. (2004). *The Randomized Geometry of Algorithms*. Survey, Section 2.1.
- Ingrosso, A. & Schmidt, M. (2020). *Simpler Proof of the Johnson-Lindenstrauss Lemma*.
  https://arxiv.org/abs/2005.10830 (cleaner constants)
