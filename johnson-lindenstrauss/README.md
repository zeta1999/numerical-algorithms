# Johnson–Lindenstrauss in Lean 4

A complete, machine-checked proof of the Johnson–Lindenstrauss lemma, built on
[mathlib](https://github.com/leanprover-community/mathlib4). Compiles end-to-end with
**no `sorry`** and depends only on the three standard foundational axioms.

- **`WALKTHROUGH.md`** — the proof explained in human language, section by section, with
  the Lean code and tactics.
- **`article.tex`** — the same as a typeset LaTeX article.
- **`JL/`** — the seven proof modules (see the table in `WALKTHROUGH.md`).
- The headline result is `JL.johnsonLindenstrauss` in `JL/UnionBound.lean`.

---

## Requirements

- The Lean 4 toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.29.0`).
  With [`elan`](https://github.com/leanprover/elan) installed, the right compiler is
  selected automatically; otherwise put a matching `lean`/`lake` on your `PATH`.
- `mathlib` and its dependencies are already vendored under `.lake/packages/` (prebuilt
  `.olean` files), so **no mathlib download or rebuild is needed** — the build below only
  compiles the eight `JL/*.lean` files.

## 1. Compile and verify the whole development

From this directory (`johnson-lindenstrauss/`):

```bash
lake build JL
```

A successful run ends with `Build completed successfully`. This type-checks every lemma
and the main theorem against the Lean kernel — i.e. it *is* the verification. Any gap
(`sorry`), type error, or unproved goal would make this command fail.

## 2. Inspect the main theorem and confirm it is axiom-clean

The surest check that nothing is assumed without proof is to print the axioms the theorem
depends on. Create a scratch file:

```bash
cat > JL/Check.lean <<'EOF'
import JL.JL
open JL
#check @johnsonLindenstrauss
#print axioms johnsonLindenstrauss
EOF
lake build JL.Check
rm JL/Check.lean
```

Expected output includes:

```
'JL.johnsonLindenstrauss' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Those three are the standard mathlib/Lean foundations. Crucially, **`sorryAx` is absent**
— if any proof were incomplete, `sorryAx` would appear here.

## 3. Build a single module

Each section compiles on its own (useful while editing):

```bash
lake build JL.LogBounds      # §1 logarithm bounds
lake build JL.GaussianMGF    # §2 MGF of a squared normal
lake build JL.ChiSq          # §3 chi-squared MGF
lake build JL.TailBounds     # §4 Chernoff tail bounds
lake build JL.Projection     # §5 single-vector concentration
lake build JL.UnionBound     # §6 union bound + the JL lemma
```

## 4. (Optional) Typeset the article

```bash
pdflatex article.tex     # produces article.pdf
```

---

### Notes

- The first `lake build` after a checkout may take a little while as Lean reads the
  vendored mathlib `.olean` files; subsequent builds are incremental and fast.
- If you see toolchain errors, confirm `lean --version` reports `4.29.x`; a different
  major/minor version cannot load the vendored mathlib oleans.
