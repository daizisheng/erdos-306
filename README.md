# Erdős Problem #306: unit fractions with semiprime denominators

Paper and Lean 4 formalisation for

> S. Li, *Unit fractions with semiprime denominators: an elementary proof of Erdős Problem #306*,
> [arXiv:2609.32140](https://arxiv.org/abs/2609.32140) (2026).

**Theorem** ([Erdős Problem #306](https://www.erdosproblems.com/306)). Every positive rational
number `a/b` with `b` squarefree is a finite sum of distinct unit fractions `1/n`, where each `n`
is a product of two distinct primes.

The proof is elementary: the only inputs about primes are Chebyshev-type bounds. Its
circle-method framework is taken from Y. Tang's Lean development
([doi:10.5281/zenodo.20767390](https://doi.org/10.5281/zenodo.20767390)), which gave the first
proof of the theorem; the construction here removes its anchor-synchronisation step. See
"Relation to previous work" in §1 of the paper.

This work is a human–AI collaboration: AI tools contributed substantially to the construction,
the experiments and the writing.

## Contents

| path | |
|---|---|
| `paper/erdos306.tex`, `paper/erdos306.pdf` | the paper, as submitted to arXiv (v1, 26 Sep 2026) |
| `lean/` | the Lean 4 + Mathlib formalisation, with no `sorry`; see [`lean/README.md`](lean/README.md) |

## Lean formalisation

The formalisation is complete: no `sorry`, no axioms beyond Lean's standard three.

```lean
theorem erdos_306 (q : ℚ) (hq : 0 < q) (hsq : Squarefree q.den) :
    ∃ F : Finset ℕ, (∀ n ∈ F, ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ r ∧ n = p * r) ∧
      ∑ n ∈ F, (1 : ℚ) / n = q
```

`erdos_306_formal_conjectures` (in `lean/Erdos306/FormalConjectures.lean`) proves, verbatim,
the statement of Erdős Problem #306 in Google DeepMind's
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/306.lean)
repository (the proposition on the right of `answer(sorry) ↔ …`, so the answer is `True`):

```lean
theorem erdos_306_formal_conjectures : ∀ (q : ℚ), 0 < q → Squarefree q.den →
    ∃ k : ℕ, ∃ (n : Fin (k + 1) → ℕ), n 0 = 1 ∧ StrictMono n ∧
    (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 2 ∧ Ω (n i) = 2) ∧
    q = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i)
```

```
'Erdos306.erdos_306' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos306.erdos_306_formal_conjectures' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The paper cites Ramanujan's inequality for the Chebyshev-type lower bound of Lemma 2.1; the
arXiv v1 ancillary Lean files kept it as their one `sorry`. Only the bound for large `x` is
used, and here it is proved from Erdős' central-binomial argument (see item 10 of
"Where the formalisation differs from the paper" in `lean/README.md`).

### Building

Toolchain `leanprover/lean4:v4.29.0-rc6`, Mathlib pinned in `lean/lake-manifest.json`.

```bash
cd lean
lake exe cache get   # download prebuilt Mathlib
lake build
lake env lean Erdos306/Main.lean               # prints the axioms of erdos_306
lake env lean Erdos306/FormalConjectures.lean  # ... and of erdos_306_formal_conjectures
```
