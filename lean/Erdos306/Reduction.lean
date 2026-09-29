/-
§3 of the paper: reduction of Theorem 1.1 to small targets (Theorem 3.1) by prime dilution.
-/
import Erdos306.Construction

namespace Erdos306

open Finset

/-- `n` is a product of two distinct primes. -/
def IsSemiprime2 (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n = p * q

/-- The statement of Theorem 1.1. -/
def MainStatement : Prop :=
  ∀ q : ℚ, 0 < q → Squarefree q.den →
    ∃ F : Finset ℕ, (∀ n ∈ F, IsSemiprime2 n) ∧ ∑ n ∈ F, (1 : ℚ) / n = q

/-- **Proof of Theorem 1.1 from Theorem 3.1** (§3).  Split `a/b` into `q` equal parts
`x = a/(bq) ≤ η` for a large prime `q ∤ ab`, represent `x` with `q` different values of `y`
whose ranges `(y^8, y^9]` are disjoint, and take the union. -/
theorem thm_main_of_small
    (hsmall : ∀ τ : ℚ, 0 < τ → τ ≤ 1 / 400 → Squarefree τ.den →
      ∃ y0 : ℕ, ∀ y ≥ y0, ∃ S : Finset (ℕ × ℕ),
        (∀ p ∈ S, p.1.Prime ∧ p.2.Prime ∧ p.1 ≤ 2 * y ^ 2 ∧ y ^ 8 < p.2 ∧ p.2 ≤ y ^ 9) ∧
        ∑ p ∈ S, (1 : ℚ) / (p.1 * p.2) = τ) :
    MainStatement := by
  intro q hq hsq
  -- Step 1: choose a large prime `p ∤ ab` with `x = q/p ≤ η`.
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (400 * q.num.natAbs + q.den + 1)
  have hnum : 0 < q.num := Rat.num_pos.2 hq
  have hq_le : q ≤ (q.num.natAbs : ℚ) := by
    have h1 : (q.num.natAbs : ℚ) = (q.num : ℚ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hnum)]
    rw [h1]
    conv_lhs => rw [← Rat.num_div_den q]
    apply div_le_self (by exact_mod_cast hnum.le)
    exact_mod_cast q.den_pos
  have hbp : Nat.Coprime q.den p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have := Nat.le_of_dvd q.den_pos hdvd
    omega
  set x : ℚ := q * (p : ℚ)⁻¹ with hx
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hx0 : 0 < x := by positivity
  have hxη : x ≤ 1 / 400 := by
    rw [hx, ← div_eq_mul_inv, div_le_iff₀ hp0]
    have : (400 * q.num.natAbs : ℚ) ≤ p := by exact_mod_cast (by omega)
    linarith
  have hxsq : Squarefree x.den := by
    have h1 : x.den ∣ q.den * p := by
      have := Rat.mul_den_dvd q ((p : ℚ)⁻¹)
      rwa [Rat.inv_natCast_den, if_neg hp.ne_zero] at this
    exact Squarefree.squarefree_of_dvd h1
      ((Nat.squarefree_mul hbp).2 ⟨hsq, hp.prime.squarefree⟩)
  obtain ⟨y0, hy0⟩ := hsmall x hx0 hxη hxsq
  -- Step 2: `k` disjoint representations of `x`, one for each of `k` increasing values of `y`.
  have key : ∀ k : ℕ, ∃ F : Finset ℕ, (∀ n ∈ F, IsSemiprime2 n) ∧
      ∑ n ∈ F, (1 : ℚ) / n = k * x := by
    intro k
    induction k with
    | zero => exact ⟨∅, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨F, hF, hFsum⟩ := ih
      -- choose `y` so large that the new semiprimes exceed every element of `F`
      set y := max y0 (max (F.sup id + 1) 2) with hy
      have hy0' : y0 ≤ y := le_max_left _ _
      have hyF : F.sup id + 1 ≤ y := le_trans (le_max_left _ _) (le_max_right _ _)
      have hy2 : 2 ≤ y := le_trans (le_max_right _ _) (le_max_right _ _)
      obtain ⟨S, hS, hSsum⟩ := hy0 y hy0'
      have h2y : 2 * y ^ 2 < y ^ 8 := by
        have : y ^ 8 = y ^ 2 * y ^ 6 := by ring
        have h6 : 2 < y ^ 6 := by
          calc 2 < 2 ^ 6 := by norm_num
            _ ≤ y ^ 6 := Nat.pow_le_pow_left hy2 6
        rw [this]
        have : 0 < y ^ 2 := by positivity
        nlinarith
      have hyy : y ≤ y ^ 8 := Nat.le_self_pow (by norm_num) y
      set G := S.image (fun r : ℕ × ℕ => r.1 * r.2) with hG
      have hinj : Set.InjOn (fun r : ℕ × ℕ => r.1 * r.2) S := by
        rintro ⟨v, u⟩ hr ⟨v', u'⟩ hr' heq
        simp only at heq
        obtain ⟨hv, hu, hv2, hu8, -⟩ := hS _ hr
        obtain ⟨hv', hu', hv2', hu8', -⟩ := hS _ hr'
        simp only at hv hu hv2 hu8 hv' hu' hv2' hu8'
        have hdvd : u ∣ v' * u' := ⟨v, by rw [← heq]; ring⟩
        rcases (Nat.Prime.dvd_mul hu).1 hdvd with h | h
        · have := (Nat.prime_dvd_prime_iff_eq hu hv').1 h
          omega
        · have huu := (Nat.prime_dvd_prime_iff_eq hu hu').1 h
          subst huu
          have : v = v' := Nat.eq_of_mul_eq_mul_right hu.pos heq
          rw [this]
      have hdisj : Disjoint F G := by
        rw [Finset.disjoint_left]
        intro n hnF hnG
        obtain ⟨⟨v, u⟩, hr, rfl⟩ := Finset.mem_image.1 hnG
        obtain ⟨hv, hu, -, hu8, -⟩ := hS _ hr
        have h1 : v * u ≤ F.sup id := Finset.le_sup (f := id) hnF
        have h2 : u ≤ v * u := Nat.le_mul_of_pos_left u hv.pos
        simp only at hu8
        omega
      refine ⟨F ∪ G, ?_, ?_⟩
      · intro n hn
        rcases Finset.mem_union.1 hn with h | h
        · exact hF n h
        · obtain ⟨⟨v, u⟩, hr, rfl⟩ := Finset.mem_image.1 h
          obtain ⟨hv, hu, hv2, hu8, -⟩ := hS _ hr
          exact ⟨v, u, hv, hu, by simp only at hv2 hu8 ⊢; omega, rfl⟩
      · rw [Finset.sum_union hdisj, hFsum, hG, Finset.sum_image hinj]
        push_cast
        rw [hSsum]
        ring
  obtain ⟨F, hF, hFsum⟩ := key p
  refine ⟨F, hF, ?_⟩
  rw [hFsum, hx]
  field_simp

end Erdos306
