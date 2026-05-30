# The Johnson–Lindenstrauss Lemma, formalized in Lean 4

A complete, machine-checked proof of the Johnson–Lindenstrauss (JL) lemma, built on
[mathlib](https://github.com/leanprover-community/mathlib4). The development compiles
end-to-end with **no `sorry`** and depends only on the three standard foundational
axioms (`propext`, `Classical.choice`, `Quot.sound`).

> **Verify it yourself:**
> ```
> lake build JL
> ```
> and, for the headline result,
> ```lean
> #print axioms JL.johnsonLindenstrauss
> -- 'JL.johnsonLindenstrauss' depends on axioms: [propext, Classical.choice, Quot.sound]
> ```

---

## 1. What do we prove?

The Johnson–Lindenstrauss lemma is the mathematical engine behind dimensionality
reduction: a set of `n` points in a high-dimensional space `ℝᵈ` can be projected, by a
*random linear map*, into a much lower dimension `ℝᵐ` — with `m` depending only on `n`
and the target accuracy, **not** on `d` — while approximately preserving all pairwise
distances.

**Informal statement.** Let `0 < ε < 1`. Take `n` distinct points `x₁, …, xₙ ∈ ℝᵈ`.
Let `A` be an `m × d` matrix with i.i.d. `N(0, 1/m)` Gaussian entries (a *random
projection*). If

```
m  ≥  C · log n / ε²
```

then, with high probability, **every** pairwise squared distance is preserved up to a
factor `(1 ± ε)`:

```
(1 − ε) · ‖xᵢ − xⱼ‖²  ≤  ‖A xᵢ − A xⱼ‖²  ≤  (1 + ε) · ‖xᵢ − xⱼ‖²     for all i ≠ j.
```

The probability that this *fails* is at most `δ`, as soon as `2n²·exp(−mε²/12) ≤ δ`.

**The formal statement** (file `JL/UnionBound.lean`):

```lean
theorem johnsonLindenstrauss (n d : ℕ) (m : ℕ) (m_pos : 0 < m)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (hx : Function.Injective x)
    (ε δ : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) (hδ_pos : 0 < δ)
    (hsuff : 2 * (n : ℝ) ^ 2 * rexp (-(m : ℝ) * ε ^ 2 / 12) ≤ δ) :
    (rowLaw m d).real
      {G | ∃ i j, i ≠ j ∧
        ((1 + ε) * ‖x i - x j‖ ^ 2 ≤ (1 / (m : ℝ)) * ∑ k, ⟪x i - x j, G k⟫_ℝ ^ 2
         ∨ (1 / (m : ℝ)) * ∑ k, ⟪x i - x j, G k⟫_ℝ ^ 2 ≤ (1 - ε) * ‖x i - x j‖ ^ 2)}
      ≤ δ
```

Here:
- `rowLaw m d` is the probability law of the random projection, modelled as `m`
  independent standard-Gaussian **rows** `G = (G₁, …, Gₘ)`, each `Gₖ ∈ ℝᵈ`.
- The projected squared norm of a vector `v` is `(1/m)·∑ₖ ⟪v, Gₖ⟫²`, which is exactly
  `‖Av‖²` for `A = G/√m`.
- `μ.real S = (μ S).toReal` is the probability of the event `S` as a real number.
- The braced set is the **bad event**: "some pair is distorted by more than `ε`". The
  theorem bounds its probability by `δ`.

---

## 2. The plan

The classical proof (Dasgupta–Gupta 1999) factors cleanly into six steps, which are
exactly the six files of this development. Each step is a self-contained, independently
compiled module of small lemmas.

| File | Result |
|------|--------|
| `JL/LogBounds.lean`   | §1 elementary `log` inequalities |
| `JL/GaussianMGF.lean` | §2 `E[exp(t Z²)] = (1−2t)^{−1/2}` for `Z ∼ N(0,1)` |
| `JL/Basic.lean` + `JL/ChiSq.lean` | §3 the chi-squared law and its MGF `(1−2t)^{−m/2}` |
| `JL/TailBounds.lean`  | §4 Chernoff tail bounds for `χ²ₘ` |
| `JL/Projection.lean`  | §5 single-vector concentration |
| `JL/UnionBound.lean`  | §6 union bound ⇒ the JL lemma |

The logical spine is:

```
χ² MGF  ──Chernoff──▶  tail bounds  ──scale──▶  one vector concentrates
                                                      │ union bound over n² pairs
                                                      ▼
                                          all distances preserved (JL)
```

We now walk through each step: **the mathematics**, then **the Lean** and the key
tactics.

---

## §1 — Logarithm bounds (`JL/LogBounds.lean`)

**Mathematics.** The Chernoff exponents below are `ε − log(1+ε)` and `−(ε + log(1−ε))`.
We need quantitative lower bounds on these. Integrating the elementary pointwise
inequality `1/(1+x) ≤ 1 − x + x²` over `[0, ε]` gives

```
ε − log(1+ε)  ≥  ε²/2 − ε³/3 ,
```

and similarly `ε + log(1−ε) ≤ −ε²/2`. For `0 < ε < 1` these simplify to the clean
bound `ε²/6` used downstream:

```
ε − log(1+ε) ≥ ε²/6        ε + log(1−ε) ≤ −ε²/6 .
```

> **A subtlety we caught.** The often-quoted bound `ε − log(1+ε) ≥ ε²/3` is **false**
> near `ε = 1` (at `ε = 1` the left side is `1 − log 2 ≈ 0.307 < 1/3`). The sharp
> constant of this form that holds on **all** of `(0,1)` is `ε²/6`, since
> `ε²/2 − ε³/3 ≥ ε²/6 ⇔ 2ε²(1−ε) ≥ 0`. We use `ε²/6` throughout.

**Lean.** The headline lemma turns the analytic claim into an integral comparison:

```lean
theorem log_upper_bound {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ε - Real.log (1 + ε) ≥ ε ^ 2 / 2 - ε ^ 3 / 3 := by
  ...
  have hI1 : ∫ x in (0:ℝ)..ε, (1 - 1 / (1 + x)) = ε - Real.log (1 + ε) := by
    rw [intervalIntegral.integral_sub iiconst hint1, integral_one_div_one_add hε_pos]; simp
  have hmono : ∫ x in (0:ℝ)..ε, (x - x ^ 2) ≤ ∫ x in (0:ℝ)..ε, (1 - 1 / (1 + x)) := by
    apply intervalIntegral.integral_mono_on hε_pos.le (iiid.sub iisq) (iiconst.sub hint1)
    intro x hx; have := one_div_one_add_le hx.1; linarith
  rw [hI1, hI2] at hmono; linarith
```

Key tactics and lemmas:
- The antiderivative `∫₀^ε 1/(1+x) = log(1+ε)` is `integral_one_div_one_add`, proved by
  the substitution `intervalIntegral.integral_comp_add_left` + `integral_one_div`.
- `intervalIntegral.integral_mono_on` does the pointwise→integral comparison; the three
  integrability side-goals are discharged by `Continuous.intervalIntegrable`.
- The pointwise inequalities `one_div_one_add_le` are pure algebra: `rw [div_le_iff₀]`
  then `nlinarith`.

---

## §2 — MGF of a squared standard normal (`JL/GaussianMGF.lean`)

**Mathematics.** For `Z ∼ N(0,1)` and `t < 1/2`,

```
E[exp(t Z²)]  =  (2π)^{−1/2} ∫ exp(t x²) exp(−x²/2) dx
              =  (2π)^{−1/2} ∫ exp(−(½−t) x²) dx
              =  (2π)^{−1/2} · √(π/(½−t))  =  (1 − 2t)^{−1/2}.
```

This is the one-dimensional seed of the whole chi-squared computation.

**Lean.**

```lean
theorem mgf_sqNorm_stdNormal (t : ℝ) (ht : t < 1 / 2) :
    ∫ x : ℝ, rexp (t * x ^ 2) ∂gaussianReal 0 1 = (1 - 2 * t) ^ (-(1/2) : ℝ) := by
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero)]
  simp only [gaussianPDFReal_std, smul_eq_mul]
  ...
  rw [integral_const_mul, integral_gaussian]   -- ∫ exp(-b x²) = √(π/b)
  have key : (√(2*π))⁻¹ * √(π/(1/2 - t)) = √((1 - 2*t)⁻¹) := by
    rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]; congr 1; field_simp
  rw [key, Real.rpow_neg h_pos.le, Real.sqrt_inv, Real.sqrt_eq_rpow]
```

Key tactics and lemmas:
- `integral_gaussianReal_eq_integral_smul` rewrites the integral against the Gaussian
  measure as an integral against its density `gaussianPDFReal`.
- `integral_gaussian : ∫ exp(−b x²) = √(π/b)` is mathlib's classical Gaussian integral.
- The final radical identity is handled by *normalising both sides to* `√((1−2t)⁻¹)`:
  `Real.sqrt_inv`, `Real.sqrt_mul`, `field_simp`, then `Real.sqrt_eq_rpow` /
  `Real.rpow_neg` to land on the `rpow` form.

---

## §3 — The chi-squared distribution and its MGF (`JL/Basic.lean`, `JL/ChiSq.lean`)

**Mathematics.** `χ²ₘ` is the law of `‖g‖²` for `g ∼ N(0, Iₘ)`. Writing the standard
Gaussian on `ℝᵐ` as the pushforward of `⊗ N(0,1)` makes `‖g‖² = ∑ gᵢ²`, so the MGF
*factorises* into `m` copies of §2:

```
E[exp(t‖g‖²)]  =  ∏ᵢ E[exp(t gᵢ²)]  =  ((1−2t)^{−1/2})ᵐ  =  (1−2t)^{−m/2}.
```

**Lean.** The definition (`JL/Basic.lean`):

```lean
noncomputable def chiSq (m : ℕ) : Measure ℝ :=
  (stdGaussian (EuclideanSpace ℝ (Fin m))).map (fun x => ‖x‖ ^ 2)
```

The MGF (`JL/ChiSq.lean`):

```lean
theorem chiSq_mgf (m : ℕ) (t : ℝ) (ht : t < 1 / 2) :
    mgf id (chiSq m) t = (1 - 2 * t) ^ (-(m : ℝ) / 2) := by
  simp only [mgf, id_eq]
  rw [chiSq, integral_map (by fun_prop) (by fun_prop)]
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [norm_toLp_sq, Finset.mul_sum, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin m) (y : ℝ) => rexp (t * y ^ 2))]
  simp_rw [mgf_sqNorm_stdNormal t ht]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.rpow_natCast _ m, ← Real.rpow_mul h_pos.le]
  congr 1; push_cast; ring
```

Key tactics and lemmas:
- `map_pi_eq_stdGaussian` re-expresses `stdGaussian` as the pushforward of the product
  measure under `toLp 2`; `norm_toLp_sq` gives `‖toLp 2 x‖² = ∑ xᵢ²`.
- `integral_fintype_prod_eq_prod` is the crucial **product-measure factorisation**:
  `∫ ∏ᵢ fᵢ(xᵢ) d(⊗μ) = ∏ᵢ ∫ fᵢ`.
- The `m`-fold product `((1−2t)^{−1/2})ᵐ` becomes `(1−2t)^{−m/2}` via `rpow_natCast`
  and `rpow_mul`.

---

## §4 — Chernoff tail bounds (`JL/TailBounds.lean`)

**Mathematics.** From `E[exp(tX)]` and Markov's inequality (the *Chernoff method*),
optimising `t`:

```
P(χ²ₘ ≥ (1+ε)m)  ≤  exp(−(m/2)(ε − log(1+ε)))  ≤  exp(−mε²/12),
P(χ²ₘ ≤ (1−ε)m)  ≤  exp( (m/2)(ε + log(1−ε)))  ≤  exp(−mε²/12).
```

The optimal parameters are `t = ε/(2(1+ε))` (upper) and `t = −ε/(2(1−ε))` (lower); the
simplification uses §1.

**Lean.** Probabilities are taken on the real side (`μ.real`), matching mathlib's
Chernoff lemmas `measure_ge_le_exp_mul_mgf` / `measure_le_le_exp_mul_mgf`:

```lean
theorem chiSq_upperTail (m : ℕ) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    (chiSq m).real {x | (1 + ε) * (m : ℝ) ≤ x}
      ≤ rexp (-(m : ℝ) * (ε - Real.log (1 + ε)) / 2) := by
  set t : ℝ := ε / (2 * (1 + ε))
  have hch := measure_ge_le_exp_mul_mgf (X := id) (μ := chiSq m) ((1 + ε) * (m : ℝ)) h0.le h_int
  rw [chiSq_mgf m t h12] at hch
  refine hch.trans ?_
  rw [Real.rpow_def_of_pos hpos, ← Real.exp_add]
  apply le_of_eq; congr 1
  have hbase : 1 - 2 * t = (1 + ε)⁻¹ := by rw [ht_def]; field_simp; ring
  rw [hbase, Real.log_inv, ht_def]; field_simp; ring
```

Key tactics and lemmas:
- Integrability `integrable_exp_mul_chiSq` is obtained "for free": the MGF is finite and
  nonzero, so the integrand cannot be non-integrable (`integral_undef` contrapositive).
- `Real.rpow_def_of_pos` converts the `rpow` MGF to `exp(log(…)·…)`, after which the
  exponent identity is pure algebra (`field_simp; ring`).
- The simplified `exp(−mε²/12)` forms chain through §1 with `Real.exp_le_exp.mpr`.

---

## §5 — Single-vector concentration (`JL/Projection.lean`)

**Mathematics.** For a fixed nonzero `v`, the row-Gaussian projection gives
`Av ∼ N(0, (‖v‖²/m) Iₘ)`, hence `‖Av‖² ∼ (‖v‖²/m)·χ²ₘ`. The two distortion events
`{‖Av‖² ≥ (1+ε)‖v‖²}` and `{‖Av‖² ≤ (1−ε)‖v‖²}` rescale exactly to the chi-squared
tails of §4, so

```
P( ‖Av‖² ∉ [(1−ε)‖v‖², (1+ε)‖v‖²] )  ≤  2·exp(−mε²/12).
```

**Lean.** We model the law of `‖Av‖²` as a scaled chi-squared and reduce each event by
change of variables:

```lean
noncomputable def projNormSq (m : ℕ) {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) : Measure ℝ :=
  (chiSq m).map (fun z => (‖v‖ ^ 2 / m) * z)

theorem singleVectorConcentration (m d : ℕ) (m_pos : 0 < m)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    (projNormSq m v).real ({y | (1+ε)*‖v‖^2 ≤ y} ∪ {y | y ≤ (1-ε)*‖v‖^2})
      ≤ 2 * rexp (-(m:ℝ) * ε^2 / 12) := ...
```

Key tactics and lemmas:
- `Measure.map_apply` turns the measure of a set under the scaling map into the measure
  of its preimage; the preimage is identified with a chi-squared tail by `nlinarith`.
- `measureReal_union_le` splits the two-sided event; `gcongr` applies the two §4 tail
  bounds.

---

## §6 — Union bound and the JL lemma (`JL/UnionBound.lean`)

**Mathematics.** Two ingredients:

1. **The marginal law.** With `m` i.i.d. standard-Gaussian rows, for fixed `v` the
   projected norm `(1/m)∑ₖ⟪v, Gₖ⟫²` has law exactly `projNormSq m v`. This is because
   each `⟪v, Gₖ⟫ ∼ N(0, ‖v‖²)`, independently across `k`.

2. **The union bound.** The bad event is the union, over the `≤ n²` distinct pairs, of
   the per-pair distortion events; sub-additivity of measure gives

```
P(bad)  ≤  Σ_{i≠j} 2·exp(−mε²/12)  ≤  n²·2·exp(−mε²/12)  =  2n²·exp(−mε²/12)  ≤  δ.
```

**Lean — the marginal (the technical crux).** The equality of measures

```lean
lemma rowLaw_map_projSq (m d : ℕ) (v : EuclideanSpace ℝ (Fin d)) :
    (rowLaw m d).map (fun G => (1 / (m : ℝ)) * ∑ i, ⟪v, G i⟫_ℝ ^ 2) = projNormSq m v
```

is proved by a chain of pushforwards (`Measure.map_map`, `Measure.pi_map_pi`):

1. `stdGaussian_map_inner`: `(stdGaussian).map ⟪v,·⟫ = gaussianReal 0 ‖v‖²` — from
   `IsGaussian.map_eq_gaussianReal`, with mean `0` (`integral_strongDual_stdGaussian`),
   variance `‖v‖²` (`variance_dual_stdGaussian` + `innerSL_apply_norm`).
2. `Measure.pi_map_pi` lifts this coordinate-wise to the product of rows.
3. `gaussianReal_map_const_mul` rescales `gaussianReal 0 ‖v‖²` to `‖v‖·N(0,1)`.
4. `pi_gaussianReal_map_sumSq_eq_chiSq` collapses `∑(‖v‖yᵢ)² = ‖v‖²∑yᵢ²` onto `chiSq`,
   reusing `map_pi_eq_stdGaussian` and `norm_toLp_sq`.

**Lean — the union bound.**

```lean
theorem johnsonLindenstrauss ... := by
  set S : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 ≠ p.2)
  calc (rowLaw m d).real {G | ∃ i j, i ≠ j ∧ _}
      ≤ (rowLaw m d).real (⋃ p ∈ S, badPair p) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ p ∈ S, (rowLaw m d).real (badPair p) := measureReal_biUnion_finset_le S _
    _ ≤ ∑ _p ∈ S, 2 * rexp (-(m:ℝ) * ε^2 / 12) := by
        apply Finset.sum_le_sum; intro p hp
        have hvne : x p.1 - x p.2 ≠ 0 := sub_ne_zero.mpr (fun h => hp (hx h))
        exact rowLaw_pair_bound m d m_pos _ hvne ε hε_pos hε_lt
    _ ≤ 2 * (n:ℝ)^2 * rexp (-(m:ℝ) * ε^2 / 12) := by ... (card S ≤ n²)
    _ ≤ δ := hsuff
```

Key tactics and lemmas:
- `measureReal_biUnion_finset_le` is the union bound; `Finset.sum_le_sum` applies the
  per-pair bound from `rowLaw_pair_bound` (itself a corollary of §5 via the marginal).
- Distinctness of the points (`hx : Function.Injective x`) gives `xᵢ − xⱼ ≠ 0`
  (`sub_ne_zero`), which the per-pair bound needs.
- `Finset.card_le_card (Finset.filter_subset …)` bounds the number of pairs by `n²`.

---

## 3. Notes on the formalization

- **No axioms beyond the kernel.** `#print axioms JL.johnsonLindenstrauss` reports only
  `[propext, Classical.choice, Quot.sound]` — the standard mathlib foundation. Every
  intermediate lemma (including `rowLaw_map_projSq`) was checked the same way.

- **The constant.** We obtain the explicit sufficient condition
  `2n²·exp(−mε²/12) ≤ δ`, equivalently `m ≥ 12·(log(2n²) + log(1/δ))/ε²`, i.e.
  `m = O(log n / ε²)` independent of the ambient dimension `d` — the whole point of JL.

- **Modelling choice.** The random projection is modelled by its rows
  (`rowLaw = ⊗ stdGaussian`), which makes the marginal of each projected coordinate a
  genuine 1-D Gaussian and keeps the dimension-`d` dependence entirely inside `‖v‖²`.
  The `1/√m` scaling of `A` appears as the `1/m` factor on the squared norm.

- **Design.** The proof is split into seven small files (≈ 500 lines total), each
  compiled independently, mirroring the seven steps of the mathematical argument. This
  was a deliberate choice: small lemmas are easier to prove, to read, and to repair than
  monolithic tactic blocks.

## References

- S. Dasgupta and A. Gupta, *An elementary proof of a theorem of Johnson and
  Lindenstrauss*, Random Structures & Algorithms, 2003.
- W. B. Johnson and J. Lindenstrauss, *Extensions of Lipschitz mappings into a Hilbert
  space*, Contemporary Mathematics, 1984.
