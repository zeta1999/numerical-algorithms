# JL Formalization — Repair & Completion Plan (decomposed)

**Goal:** a fully compiling, end-to-end proof of the Johnson–Lindenstrauss lemma in
`nr1/lean/JL/`, with **no `sorry`**.

**Method (per user directive):** step by step, **split into many small files and
small lemmas**. Never wrestle a giant monolithic tactic block — if a proof is hard,
break it into named helper lemmas, each of which compiles on its own.

**Environment:** build inside `nr1/lean` (toolchain `v4.29.0`, mathlib fully built).
Build a single module with `lake build JL.<Module>`. The current monolith
`JL/JL.lean` is replaced by the split below.

---

## File / module layout (under `nr1/lean/JL/`)

```
JL/
  Basic.lean        §0  shared opens, notation, the chiSq definition + prob-measure
  LogBounds.lean    §1  Taylor/log inequalities (pure real analysis)
  GaussianMGF.lean  §2  mgf of a single squared N(0,1):  ∫ exp(t x²) dN(0,1) = (1-2t)^(-1/2)
  ChiSq.lean        §3  chiSq_mgf: mgf id (chiSq m) t = (1-2t)^(-m/2)   (product factorization)
  TailBounds.lean   §4  Chernoff upper/lower tail bounds + simplified ε²/3 forms
  Projection.lean   §5  random-projection model; single-vector concentration
  UnionBound.lean   §6  union bound over pairs → johnsonLindenstrauss
  JL.lean           top: `import`s all of the above (thin aggregator)
```

`nr1/lean/lakefile.toml`: change the `JL` lib to `globs = ["JL"]` (or build module
targets directly) so it does not look for a nonexistent root `JL.lean`.

**Typing convention (decided):** measures of sets are `ℝ≥0∞`. State every tail/JL
bound on the **real** side using `(μ S).toReal ≤ exp (…)`, matching mathlib's
`measure_ge_le_exp_mul_mgf` (which is already `.toReal`-flavored). This removes the
`ℝ` vs `ℝ≥0∞` mismatches that break §4 today.

---

## §0 `Basic.lean`
- `open MeasureTheory ProbabilityTheory NNReal Real Set` + scoped `RealInnerProductSpace`.
- `noncomputable def chiSq (m : ℕ) : Measure ℝ := (stdGaussian (EuclideanSpace ℝ (Fin m))).map (fun x => ‖x‖ ^ 2)`
  (use `fun x => ‖x‖ ^ 2`, **not** the non-parsing `(‖·‖²)`).
- `lemma measurable_normSq …`, `lemma isProbMeasure_chiSq (m) : IsProbabilityMeasure (chiSq m)`.

## §1 `LogBounds.lean`  (no measure theory; fastest to green)
Small lemmas, then the headline bounds:
- `lemma one_div_one_add_le {x} (hx : 0 ≤ x) : 1/(1+x) ≤ 1 - x + x^2`  (`div_le_iff₀`).
- `lemma one_add_le_one_div_one_sub {x} (0 ≤ x) (x<1) : 1 + x ≤ 1/(1-x)` (`le_div_iff₀`).
- `theorem log_upper_bound`  ε - log(1+ε) ≥ ε²/2 - ε³/3   — integral comparison via
  `intervalIntegral.integral_mono_on` (replaces nonexistent `integral_le_integral`),
  `integral_one_div_one_add_*` / `← integral_log` for the antiderivative.
- `theorem log_lower_bound`  ε + log(1-ε) ≤ -ε²/2.
- `theorem log_upper_bound_simplified` ≥ ε²/3 ; `log_lower_bound_simplified` ≤ -ε²/3 (`nlinarith`).

## §2 `GaussianMGF.lean`
Split the current monolith into:
- `lemma gaussianReal_eq_withDensity : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1)`.
- `lemma integral_wrt_gaussianReal (f) : ∫ x, f x ∂gaussianReal 0 1 = ∫ x, f x * gaussianPDF 0 1 x` (correct `withDensity` integral lemma name; not `withDensity_apply_of_pos`).
- `lemma gaussianPDF_eq : gaussianPDF 0 1 x = (√(2π))⁻¹ * exp(-(x²)/2)`.
- `lemma integral_exp_neg_half_sub (ht : t < 1/2) : ∫ x, exp(-(1/2 - t) x²) = √(π/(1/2 - t))` (`integral_exp_neg_mul_sq`).
- `theorem mgf_sqNorm_stdNormal (ht : t < 1/2) : ∫ x, exp(t x²) ∂gaussianReal 0 1 = (1-2t)^(-1/2)`.
  Fix Lean3 lambda syntax `fun x : ℝ,` → `fun x : ℝ =>` throughout. Isolate the final
  √/`field_simp` algebra into its own `have`/lemma so it can be debugged alone.

## §3 `ChiSq.lean`
- `lemma stdGaussian_eq_map_pi : stdGaussian (EuclideanSpace ℝ (Fin m)) = (Measure.infinitePi …).map (toLp 2)` via `map_pi_eq_stdGaussian` (add import `Mathlib.MeasureTheory.Integral.Pi`; qualify `infinitePi`/`toLp`).
- `lemma norm_toLp_sq (x : Fin m → ℝ) : ‖toLp 2 x‖^2 = ∑ i, x i ^ 2`  (`EuclideanSpace.norm_eq`).
- `lemma infinitePi_eq_pi : Measure.infinitePi (fun _:Fin m => μ) = Measure.pi …` (finite index).
- `lemma integral_exp_chiSq_factor : ∫ exp(t‖·‖²) dstdGaussian = ∏ i, ∫ exp(t y²) dN(0,1)` (`integral_fintype_prod_eq_prod`).
- `theorem chiSq_mgf (hm) (ht : t < 1/2) : mgf id (chiSq m) t = (1-2t)^(-m/2)`
  (state via `mgf`, unfold `mgf` to the integral; combine the lemmas above + §2).

## §4 `TailBounds.lean`
- `lemma integrable_exp_mul_chiSq (ht : t < 1/2) : Integrable (fun x => exp (t*x)) (chiSq m)` — from finite mgf.
- `lemma mgf_chiSq_eval` helper rewrites `mgf id (chiSq m) t` at the chosen `t`.
- `theorem chiSq_upperTail`  `(chiSq m {x | (1+ε)m ≤ x}).toReal ≤ exp(-(m)(ε-log(1+ε))/2)`
  via `measure_ge_le_exp_mul_mgf` at `t = ε/(2(1+ε))`; isolate each algebra step
  (`-t(1+ε)m = -εm/2`, `mgf = (1+ε)^(m/2)`, `exp+rpow` merge) as its own `have`.
- `theorem chiSq_lowerTail` at `t = ε/(2(1-ε))` via `measure_le_le_exp_mul_mgf`.
- `theorem chiSq_upperTail_simplified` / `chiSq_lowerTail_simplified` ≤ `exp(-mε²/3)` (chain with §1).

## §5 `Projection.lean`  (first genuinely new content)
Model `A v` for fixed `v` **without** building the full m×d matrix measure:
- `noncomputable def projNormSq (m) (v) : Measure ℝ := (stdGaussian (EuclideanSpace ℝ (Fin m))).map (fun g => (‖v‖^2 / m) * ‖g‖^2)` — this is exactly the law of `‖Av‖²` since `Av ~ N(0,(‖v‖²/m) I_m)`.
- `lemma projNormSq_eq_map_chiSq : projNormSq m v = (chiSq m).map (fun z => (‖v‖^2/m) * z)`.
- `lemma projNormSq_upperTail` / `lowerTail`: rewrite the distortion events
  `{‖Av‖² ≥ (1+ε)‖v‖²} = {‖g‖² ≥ (1+ε)m}` (scaling), apply §4.
- `theorem singleVectorConcentration (hv : v ≠ 0) … : (projNormSq m v {y | distortion}).toReal ≤ 2*exp(-mε²/3)` via `measure_union_le` of the two tails.

## §6 `UnionBound.lean`  (heaviest; break aggressively)
- `noncomputable def jlMatrixMeasure (m d) : Measure (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin d))` (or a `Matrix`/`Fin m × Fin d → ℝ` Gaussian, scaled by `1/√m`). Pick the representation that makes the marginal lemma cleanest.
- **Marginal lemma** (crux): `lemma jl_marginal (v ≠ 0) : (jlMatrixMeasure m d).map (fun A => ‖A v‖^2) = projNormSq m v` — uses that a linear image of a standard Gaussian is Gaussian (`stdGaussian` pushforward / `variance_dual_stdGaussian`). Break into: linearity of `A ↦ A v`, identification of the pushforward covariance, reduction to `projNormSq`.
- `lemma jl_pair_bad_prob (xi xj, xi≠xj) : P(pair (i,j) distorted) ≤ 2 exp(-mε²/3)` (combine marginal + §5).
- `lemma jl_union_bound : P(∃ i<j distorted) ≤ (n.choose 2) * 2 * exp(-mε²/3)` via iterated `measure_biUnion_le` / `measure_union_le`.
- `lemma count_le : (n.choose 2 : ℝ) ≤ n^2 / 2` ; arithmetic `m ≥ 6(ln n + ln(1/δ))/ε² ⇒ n² exp(-mε²/3) ≤ δ`.
- `theorem johnsonLindenstrauss …` : assemble; conclude `P(all pairs good) ≥ 1 - δ`.

---

## Execution order & checkpoints (one green build per step)
0. Restructure files + fix lakefile; empty skeletons compile.
1. `LogBounds.lean` green.
2. `Basic.lean` green.
3. `GaussianMGF.lean` green.
4. `ChiSq.lean` green.
5. `TailBounds.lean` green.
6. `Projection.lean` green.
7. `UnionBound.lean` green → `JL.lean` aggregator green → `#print axioms johnsonLindenstrauss` clean.

After each step: `lake build JL.<Module>` must succeed with zero errors and zero `sorry`
before moving on. Use the `lean4` skill / proof tactics per lemma; keep lemmas tiny.

## Post-completion phases (after end-to-end compile, no sorry)
- **Commit cadence:** commit often once things compile; **never push**.
- **Phase 7:** move the JL demonstration into its own dedicated folder, erasing the old
  `jl/` (and consolidating the in-`nr1` copy) — keep the build working.
- **Phase 8:** an explanatory `.md` article — human language first (what we demonstrate,
  the plan: we prove X to achieve Y), then the Lean4 code with its tactics explained.
- **Phase 9:** a LaTeX article covering the whole development in polished article format:
  motivation/plan → the mathematics → the Lean4 proof with tactics.

## Known API fixes (v4.29 mathlib)
`div_le_iff`→`div_le_iff₀`; `le_div_iff`→`le_div_iff₀`; `integral_le_integral`→`intervalIntegral.integral_mono_on`;
Lean3 `fun x : T,`→`fun x : T =>`; `(‖·‖²)`→`fun x => ‖x‖^2`; `withDensity_apply_of_pos`→correct withDensity integral lemma;
qualify `infinitePi`/`toLp` + import `MeasureTheory.Integral.Pi`; tail-bound statements use `(μ S).toReal`.
