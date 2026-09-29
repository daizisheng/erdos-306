# Lean 4 formalisation of the proof in `erdos306.tex`

This is a Lean 4 + Mathlib formalisation of the proof of Erdős Problem #306 in
S. Li, *Unit fractions with semiprime denominators: an elementary proof of Erdős Problem #306*
(the main file of this arXiv submission, `erdos306.tex`). The main theorem is:

> every positive rational `q` whose reduced denominator is squarefree is a sum `∑_{n∈F} 1/n`
> over a finite set `F` of distinct natural numbers, each a product of two distinct primes.

The development follows the paper's own proof, lemma by lemma. It is not an independent
re-proof of the theorem. The paper's steps all appear, under the paper's names:

- the reduction to small targets by prime dilution (§3);
- the construction `V = {2} ∪ B ∪ W`, `U = U(Y)` and the tuning lemma (§4);
- the geometric-sum counting formula (§5);
- the `V × U` table and the three cases (§6);
- the major arcs by positivity (§7);
- the column lemmas (§8);
- the minor arcs (§9).

Every paper-level lemma has a docstring that cites its number in the compiled paper and
states it in words.

## Building

This directory is a self-contained Lake project (toolchain `leanprover/lean4:v4.29.0-rc6`,
Mathlib pinned to commit `921b8d39f71a5c813b526f38e4033417d40b4c3d` in `lake-manifest.json`).

```bash
cd lean
lake exe cache get   # download prebuilt Mathlib
lake build           # builds the library Erdos306
```

`Erdos306/Main.lean` ends with `#print axioms` for the two main theorems, whose output is shown
below.

The exact statements of the two main theorems are at the end of `Erdos306/Main.lean`; the
hypothesis `RamanujanInequality` is defined in `Erdos306/External.lean`. To re-print the
axioms after building, run `lake env lean Erdos306/Main.lean`.

## Files (in dependency order)

| file | paper | contents |
|---|---|---|
| `Erdos306/Basic.lean` | §5, §8 | `nint x = ‖x‖` (distance to the nearest integer) and `ee x = e(x)`, with basic facts |
| `Erdos306/External.lean` | Lemma 2.1 | **the only `sorry`**: Ramanujan's inequality (`RamanujanInequality`, `ramanujan_theta`) |
| `Erdos306/Primes.lean` | §2 | `lem_cheb_erdos` and `lem_cheb` (Lemma 2.1), `cor_mertens` (Corollary 2.2) |
| `Erdos306/Construction.lean` | §4 | `Bset`, `Wset`, `Vset`, `Uset`, `HV`, `Aset`, `mu`, `sigma`, `Lnum`, `delta`, `eps`, `deltaA`; the structures `Large` (every "for `y` large" inequality) and `Tuned`; eq. (1) (`prod_V_le`, `HV_bounds`); `lem_tuning` (Lemma 4.1); `sigma_le_half` and `sigma_eq_of_congr` (a congruence mod 1 forces equality) |
| `Erdos306/Counting.lean` | §5 | `freq`, `phi`, `Ncount`; `lem_geom` (geometric sum), `eq_N` (formula (2)), `eq_half` (eq. (3)), `norm_phi` |
| `Erdos306/Table.lean` | §6 | `PV`, `crt`, `phase`, `Fcol` (`F_u`), `Scol` (`S_u`), `Coherent`, `CaseI`/`CaseII`/`CaseIII`; `coherent_unique`, `three_cases`, `caseI_iff` (case I is exactly `|h| ≤ y^7`), `label_inj`, `norm_phi_eq_prod_Fcol`, `eq_factor` (eq. (4)) |
| `Erdos306/Major.lean` | §7 | `major_step1`, `major_step2`, `prop_major` (Prop. 7.1: `Σ_maj` is real and `≥ 1/L`) |
| `Erdos306/Columns.lean` | §8 | `lem_cos` (Lemma 8.1), `eq_pf` (eq. (5)), `Invisible`, `lem_count` (Lemma 8.2), `lem_unique` (Lemma 8.3), `heavy_unique`, `lem_admissible` (Lemma 8.4), `coherent_of_admissible` |
| `Erdos306/Minor.lean` | §9 | `caseIII_column`, `caseIII_total`, `caseII_single`, `caseII_total`, `minor_le_labels`, `prop_minor` (Prop. 9.1) |
| `Erdos306/Asymptotics.lean` | throughout | `eps_le` (the bound on `ε` in §8.1); `eventually_large`: every field of `Large τ y` holds for all large `y` |
| `Erdos306/Core.lean` | §4–§9 | `prop_core` (Prop. 4.2) and `thm_small` (Thm. 3.1) |
| `Erdos306/Reduction.lean` | §3 | `thm_main_of_small`: proof of Thm. 1.1 from Thm. 3.1 |
| `Erdos306/Main.lean` | Thm. 1.1 | `erdos_306_of_ramanujan` (sorry-free) and `erdos_306` |

## Status

The whole development builds. The only `sorry` is the proof of Ramanujan's inequality, which
the paper cites and does not prove.

```
'Erdos306.erdos_306_of_ramanujan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos306.erdos_306' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

`erdos_306_of_ramanujan` takes the statement of Ramanujan's inequality as a hypothesis and uses
no `sorry`. `erdos_306` discharges that hypothesis with `External.ramanujan_theta`.

### Sorry inventory

**(a) External facts that the paper cites:**
- `External.ramanujan_theta : RamanujanInequality`. This is Ramanujan (1919): for every real
  `x > 300`, `θ(x) − θ(x/2) > x/6 − 3√x`, where `θ` is `Chebyshev.theta`. Mathlib does not
  yet have a Chebyshev lower bound.

Erdős' bound `∏_{p≤x} p ≤ 4^x` is Mathlib's `primorial_le_4_pow`. The limit
`∑ 1/j → log(9/8)` is not needed: the proof uses the elementary bound
`∑_{a≤j<b} 1/j ≥ log(b/a)`, proved in `Primes.harmonic_ge_log`.

**(b) Gaps in our own proof:** none.

## Where the formalisation differs from the paper

These are differences of presentation; the mathematics is the same.

1. **`y` is a natural number**, so `y^7` is an integer. The endpoint `Y` of `U(Y)` is a natural
   number in `[y^8, y^9]` rather than a prime, which gives the same set `U`. The tuning lemma
   takes `Y` maximal with `μ(Y) ≤ τ`.
2. **"For `y` sufficiently large"**: every such inequality in the paper is one field of
   `Large τ y`, with a comment saying where it is used. `eventually_large` proves them all at
   once, and the explicit threshold is about `2·10^11` together with bounds depending on `τ`.
3. **Frequencies** are `h ∈ (−⌊L/2⌋, L − ⌊L/2⌋]`, which is the paper's `(−L/2, L/2]` because `L`
   is even.
4. **Row labels** are stored as one residue `ξ = h mod P_V` with `P_V = ∏_{v∈V} v`, so
   `ξ_v = ξ mod v`. Column labels are residues `ζ_u ∈ [0, u)`. The phase `φ_{vu}(ξ, ζ_u)` is
   `J/(uv)` for the CRT integer `J` (`Table.crt`).
5. **Only half of the CRT bijection is used.** The minor-arc bound needs only that the label
   map `h ↦ (ξ, ζ)` is injective on frequencies (`label_inj`), because every summand is
   nonnegative. Surjectivity is never needed.
6. **No inverses mod `u`.** "`‖s w̄/u‖ ≤ δ`" is written as "`t w ≡ s (mod u)` for some integer
   `|t| ≤ δu`" (`Columns.Invisible`). The two are equivalent. In Lemma 8.2 the bound
   `|s + uℓ| = |t| w ≤ y^{11}` is read off directly.
7. **Case II expansion.** The paper expands `∏(F_u + R_u)` over the set `T` of mismatched
   columns. Here the same bound `∏(a_u + R_u) − ∏ a_u ≤ (1 + Yε)^{|U|} − 1` is proved by
   induction (`Minor.prod_add_sub_prod_le`).
8. **Prop. 7.1.** Realness is proved by the pairing `M ↔ −M`, which kills the imaginary part.
   The bound `Re Σ_maj ≥ 1/L` is proved termwise. `prop_core` uses only the real part.
9. **§3 reduction.** The `q` representations are added one at a time. Each new `y` is chosen
   with `y^8` larger than every semiprime already used, so the ranges `(y_i^8, y_i^9]` are
   disjoint, as in the paper.

## Remarks on the paper

The formalisation found no mathematical errors or gaps. Every inequality the paper states
"for `y` large" is true and was proved. Four small points:

- Eq. (1), `|W| ≥ y²/(8 log y)`, follows from Lemma 2.1 only once `y ≥ 2^{3.5}`. This is
  covered by "`y` large".
- The uniqueness of `M` for coherent labels (§6.2) needs `∏_V v > 2y^7`. This holds because
  `|W| ≥ 100` for large `y`; in Lean it follows from eq. (1) together with the numerical
  condition of Lemma 8.2 (`Table.card_W_ge`).
- The threshold in Theorem 3.1 is "large in terms of `b`". The proof actually uses `τ` itself
  (for example `H_V/(2y^8) < τ/2`), but since `τ ≥ 1/b` it can be expressed in terms of `b`
  alone. The Lean statement quantifies over `τ` directly.
- The hypothesis `0 < τ` is not needed for Propositions 4.2, 7.1 and 9.1 once `Large` and
  `Tuned` are assumed.
