/-
Main theorem (Theorem 1.1 of the paper): Erdős Problem #306.
-/
import Erdos306.Core
import Erdos306.Reduction

namespace Erdos306

/-- **Theorem 1.1 (Erdős Problem #306), assuming Ramanujan's inequality.**  Every positive
rational number whose reduced denominator is squarefree is a finite sum of reciprocals of
pairwise distinct natural numbers, each a product of two distinct primes.  This theorem is
sorry-free; its only hypothesis is the statement of Ramanujan's inequality, cited in Lemma 2.1. -/
theorem erdos_306_of_ramanujan (hR : RamanujanInequality) (q : ℚ) (hq : 0 < q)
    (hsq : Squarefree q.den) :
    ∃ F : Finset ℕ, (∀ n ∈ F, ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ r ∧ n = p * r) ∧
      ∑ n ∈ F, (1 : ℚ) / n = q := by
  obtain ⟨F, hF, hsum⟩ := thm_main_of_small (thm_small hR) q hq hsq
  refine ⟨F, fun n hn => ?_, hsum⟩
  obtain ⟨p, r, hp, hr, hpr, rfl⟩ := hF n hn
  exact ⟨p, r, hp, hr, hpr.ne, rfl⟩

/-- **Theorem 1.1 (Erdős Problem #306)**, with Ramanujan's inequality discharged by the
external (sorried) fact `ramanujan_theta`. -/
theorem erdos_306 (q : ℚ) (hq : 0 < q) (hsq : Squarefree q.den) :
    ∃ F : Finset ℕ, (∀ n ∈ F, ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ r ∧ n = p * r) ∧
      ∑ n ∈ F, (1 : ℚ) / n = q :=
  erdos_306_of_ramanujan ramanujan_theta q hq hsq

end Erdos306

#print axioms Erdos306.erdos_306_of_ramanujan
#print axioms Erdos306.erdos_306
