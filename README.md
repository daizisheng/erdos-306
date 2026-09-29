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
| `lean/` | the Lean 4 + Mathlib formalisation (identical to the arXiv ancillary files); see [`lean/README.md`](lean/README.md) |

## Lean formalisation

```lean
theorem erdos_306_of_ramanujan (hR : RamanujanInequality) (q : ℚ) (hq : 0 < q)
    (hsq : Squarefree q.den) :
    ∃ F : Finset ℕ, (∀ n ∈ F, ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ r ∧ n = p * r) ∧
      ∑ n ∈ F, (1 : ℚ) / n = q
```

`RamanujanInequality` is the statement of Ramanujan's inequality (1919): for every real
`x > 300`, `θ(x) − θ(x/2) > x/6 − 3√x`. The paper cites it and does not prove it; Mathlib does
not yet contain a Chebyshev lower bound. `erdos_306_of_ramanujan` takes it as a hypothesis and
uses no `sorry`. `erdos_306` has the same conclusion with the hypothesis discharged by
`ramanujan_theta`, whose proof is the development's only `sorry`.

```
'Erdos306.erdos_306_of_ramanujan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos306.erdos_306' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

### Building

Toolchain `leanprover/lean4:v4.29.0-rc6`, Mathlib pinned in `lean/lake-manifest.json`.

```bash
cd lean
lake exe cache get   # download prebuilt Mathlib
lake build
lake env lean Erdos306/Main.lean   # prints the axioms above
```
