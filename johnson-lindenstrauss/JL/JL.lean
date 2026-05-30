import JL.Basic
import JL.LogBounds
import JL.GaussianMGF
import JL.ChiSq
import JL.TailBounds
import JL.Projection
import JL.UnionBound

/-!
# Johnson–Lindenstrauss Lemma — top-level aggregator

This module re-exports the full development.  See the individual files:

* `JL.Basic`       — the chi-squared distribution `χ²_m`.
* `JL.LogBounds`   — Taylor/logarithm inequalities.
* `JL.GaussianMGF` — MGF of a squared standard normal.
* `JL.ChiSq`       — `mgf id (χ²_m) t = (1-2t)^(-m/2)`.
* `JL.TailBounds`  — Chernoff tail bounds for `χ²_m`.
* `JL.Projection`  — single-vector concentration.
* `JL.UnionBound`  — the union bound and `johnsonLindenstrauss`.
-/
