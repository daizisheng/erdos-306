/-
Main theorem (Theorem 1.1 of the paper): Erdős Problem #306.
-/
import Erdos306.Core
import Erdos306.Reduction

namespace Erdos306

/-- **Theorem 1.1 (Erdős Problem #306).**  Every positive rational number whose reduced
denominator is squarefree is a finite sum of reciprocals of pairwise distinct natural numbers,
each a product of two distinct primes. -/
theorem erdos_306 (q : ℚ) (hq : 0 < q) (hsq : Squarefree q.den) :
    ∃ F : Finset ℕ, (∀ n ∈ F, ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ r ∧ n = p * r) ∧
      ∑ n ∈ F, (1 : ℚ) / n = q := by
  obtain ⟨F, hF, hsum⟩ := thm_main_of_small thm_small q hq hsq
  refine ⟨F, fun n hn => ?_, hsum⟩
  obtain ⟨p, r, hp, hr, hpr, rfl⟩ := hF n hn
  exact ⟨p, r, hp, hr, hpr.ne, rfl⟩

end Erdos306

#print axioms Erdos306.erdos_306
