/-
Assembly of §§4–9: Proposition 4.2 and Theorem 3.1 (small targets).
-/
import Erdos306.Major
import Erdos306.Minor
import Erdos306.Asymptotics

namespace Erdos306

open Real Finset

attribute [local instance] Classical.propDecidable

variable {τ : ℚ} {y Y : ℕ}

/-- **Proposition 4.2.**  There is `S ⊆ A` with `σ(S) ≡ τ (mod 1)`.
(Split formula (2) into the three cases: case I contributes `≥ 1/L` (Prop. 7.1), cases II and III at
most `1/(2L)` in absolute value (Prop. 9.1); so `N > 0`.) -/
theorem prop_core (hsq : Squarefree τ.den) (hL : Large τ y) (hT : Tuned τ y Y) :
    ∃ S ⊆ Aset τ y Y, ∃ k : ℤ, sigma S - τ = k := by
  set L := Lnum τ y Y with hLdef
  set A := Aset τ y Y with hAdef
  set K : ℤ := (y : ℤ) ^ 7 with hK
  have hLpos : 0 < L := by
    have h1 := L_gt (Y := Y) hL
    have h2 : (0 : ℤ) ≤ (y : ℤ) ^ 7 := by positivity
    have : (0 : ℤ) < (L : ℤ) := by rw [hLdef]; linarith
    exact_mod_cast this
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hA : ∀ p ∈ A, 0 < p.1 * p.2 ∧ p.1 * p.2 ∣ L := by
    intro p hp
    refine ⟨?_, edge_dvd_L hL hp⟩
    have h1 := (prime_of_mem_Vset (mem_Aset.1 hp).1).pos
    have h2 := (prime_of_mem_Uset (mem_Aset.1 hp).2).pos
    positivity
  have hN := eq_N A τ L hLpos hA (den_dvd_L hsq)
  -- split the frequencies into major arcs `|h| ≤ y^7` and the rest
  set f : ℤ → ℂ := fun h => ee (-((h : ℝ) * τ)) * phi A h with hf
  have hsplit := Finset.sum_filter_add_sum_filter_not (freq L) (fun h => |h| ≤ K) f
  have hmaj : (freq L).filter (fun h => |h| ≤ K) = Finset.Icc (-K) K := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨-, hh⟩; exact abs_le.1 hh
    · intro hh
      exact ⟨mem_freq_of_small hL (abs_le.2 hh), abs_le.2 hh⟩
  rw [hmaj] at hsplit
  -- bound on the minor arcs
  have hminor : ‖∑ h ∈ (freq L).filter (fun h => ¬ |h| ≤ K), f h‖ ≤ 1 / 2 := by
    calc ‖∑ h ∈ (freq L).filter (fun h => ¬ |h| ≤ K), f h‖
        ≤ ∑ h ∈ (freq L).filter (fun h => ¬ |h| ≤ K), ‖f h‖ := norm_sum_le _ _
      _ = ∑ h ∈ (freq L).filter (fun h => ¬ |h| ≤ K), ‖phi A h‖ := by
          refine Finset.sum_congr rfl (fun h _ => ?_)
          simp [hf, norm_ee]
      _ ≤ ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h ∨ CaseIII τ y h), ‖phi A h‖ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro h hh
            simp only [Finset.mem_filter] at hh ⊢
            refine ⟨hh.1, ?_⟩
            rcases (three_cases (Y := Y) hL h).1 with h1 | h1
            · exact absurd ((caseI_iff hL hh.1).1 h1) hh.2
            · exact h1
          · intros; exact norm_nonneg _
      _ ≤ 1 / 2 := prop_minor hL hT
  have hmajor := prop_major hL hT
  -- real parts
  have hre : ((Ncount A τ : ℂ) / 2 ^ A.card).re ≥ 1 / (2 * L) := by
    rw [hN, ← hsplit, mul_add]
    have e1 : (1 / (L : ℂ)) * ∑ h ∈ Finset.Icc (-K) K, f h = SigmaMaj τ y Y := rfl
    rw [Complex.add_re, e1]
    have e2 : ((1 / (L : ℂ)) * ∑ h ∈ (freq L).filter (fun h => ¬ |h| ≤ K), f h).re
        ≥ -(1 / (2 * L)) := by
      set R := ∑ h ∈ (freq L).filter (fun h => ¬ |h| ≤ K), f h
      have : (1 / (L : ℂ)) * R = ((1 / (L : ℝ) : ℝ) : ℂ) * R := by push_cast; ring
      rw [this, Complex.re_ofReal_mul]
      have hRre : -‖R‖ ≤ R.re := by
        have := Complex.abs_re_le_norm R
        linarith [neg_abs_le R.re]
      have hpos : (0 : ℝ) ≤ 1 / L := by positivity
      have : -(1 / (2 * (L : ℝ))) = 1 / L * (-(1 / 2)) := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left (by linarith) hpos
    have e3 := hmajor.2
    have : 1 / (L : ℝ) - 1 / (2 * L) = 1 / (2 * L) := by field_simp; ring
    linarith
  have hNpos : 0 < Ncount A τ := by
    by_contra hcon
    push_neg at hcon
    have : Ncount A τ = 0 := by omega
    rw [this] at hre
    simp at hre
    have : (0 : ℝ) < (L : ℝ)⁻¹ * 2⁻¹ := by positivity
    linarith
  unfold Ncount at hNpos
  obtain ⟨S, hS⟩ := Finset.card_pos.1 hNpos
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS
  exact ⟨S, hS.1, hS.2⟩

/-- The statement of Theorem 3.1 (small targets). -/
def SmallTargets : Prop :=
  ∀ τ : ℚ, 0 < τ → τ ≤ 1 / 400 → Squarefree τ.den →
    ∃ y0 : ℕ, ∀ y ≥ y0, ∃ S : Finset (ℕ × ℕ),
      (∀ p ∈ S, p.1.Prime ∧ p.2.Prime ∧ p.1 ≤ 2 * y ^ 2 ∧ y ^ 8 < p.2 ∧ p.2 ≤ y ^ 9) ∧
      ∑ p ∈ S, (1 : ℚ) / (p.1 * p.2) = τ

/-- **Theorem 3.1 (Small targets).**  Let `τ = a/b ∈ (0, η]`, `η = 1/400`, with `b` squarefree.
Then for every sufficiently large `y`, `τ` is a finite sum of distinct `1/(vu)` with
`v ≤ 2y² < y^8 < u ≤ y^9` primes. -/
theorem thm_small (hR : RamanujanInequality) : SmallTargets := by
  intro τ h0 hη hsq
  obtain ⟨y0, hy0⟩ := eventually_large hR h0
  refine ⟨y0, fun y hy => ?_⟩
  have hL := hy0 y hy
  obtain ⟨Y, hT⟩ := lem_tuning h0 hη hL
  obtain ⟨S, hSA, k, hk⟩ := prop_core hsq hL hT
  refine ⟨S, fun p hp => ?_, sigma_eq_of_congr h0 hη hT hSA k hk⟩
  have hpA := mem_Aset.1 (hSA hp)
  have hv := le_of_mem_Vset hL hpA.1
  have hu := bounds_of_mem_Uset hpA.2
  exact ⟨prime_of_mem_Vset hpA.1, prime_of_mem_Uset hpA.2, hv.2, hu.1, hu.2.trans hT.hi⟩

end Erdos306
