/-
§2 of the paper: two bounds for primes.

* `lem_cheb_erdos`, `lem_cheb` — Lemma 2.1 (Chebyshev-type bounds);
* `cor_mertens`                — Corollary 2.2 (the large side carries reciprocal mass `≥ 1/50`).
-/
import Erdos306.External

namespace Erdos306

open Real Finset

/-- The primes `p` with `a < p ≤ b`. -/
def primesIn (a b : ℕ) : Finset ℕ := (Finset.Ioc a b).filter Nat.Prime

/-- Membership in `primesIn a b`. -/
lemma mem_primesIn {a b p : ℕ} : p ∈ primesIn a b ↔ a < p ∧ p ≤ b ∧ p.Prime := by
  simp [primesIn, and_assoc]

/-- **Lemma 2.1, first part** (Erdős' bound): `∏_{p ≤ x} p ≤ 4^x`.  This is Mathlib's
`primorial_le_4_pow`. -/
theorem lem_cheb_erdos (n : ℕ) : primorial n ≤ 4 ^ n := primorial_le_4_pow n

/-- **Lemma 2.1, second part**: for all sufficiently large real `x`,
`x / (7 log x) ≤ π(x) - π(x/2)`, i.e. there are at least `x/(7 log x)` primes in `(x/2, x]`.
Derived from Ramanujan's inequality (the hypothesis `hR`, proved as `ramanujan_theta`). -/
theorem lem_cheb (hR : RamanujanInequality) : ∃ x0 : ℝ, ∀ x ≥ x0,
    x / (7 * log x) ≤ ((primesIn ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) := by
  refine ⟨126 ^ 2, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) ≤ x := le_trans (by positivity) hx
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hlog : 0 < log x := Real.log_pos hx1
  -- θ(x) - θ(x/2) is the sum of `log p` over the primes of `(x/2, x]`
  have hθ : Chebyshev.theta x - Chebyshev.theta (x / 2) =
      ∑ p ∈ primesIn ⌊x / 2⌋₊ ⌊x⌋₊, log p := by
    have hmono : ⌊x / 2⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor (by linarith)
    unfold Chebyshev.theta primesIn
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hmono]
    ring
  -- each term is at most `log x`
  have hle : ∑ p ∈ primesIn ⌊x / 2⌋₊ ⌊x⌋₊, log p ≤
      ((primesIn ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) * log x := by
    rw [← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro p hp
    obtain ⟨-, hp2, hpp⟩ := mem_primesIn.1 hp
    apply Real.log_le_log (by exact_mod_cast hpp.pos)
    exact le_trans (by exact_mod_cast hp2) (Nat.floor_le hx0)
  have hram := hR x (by nlinarith)
  -- `x/6 - 3√x ≥ x/7` for `x ≥ 126²`
  have hsq : (126 : ℝ) ≤ Real.sqrt x := by
    rw [show (126 : ℝ) = Real.sqrt (126 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hss := Real.mul_self_sqrt hx0
  have h7 : x / 7 ≤ x / 6 - 3 * Real.sqrt x := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- Telescoping bound for the harmonic sum used in Corollary 2.2:
`∑_{a ≤ i < a+n} 1/(i+1) ≥ log((a+n+1)/(a+1))` (from `log(1+1/m) ≤ 1/m`). -/
lemma harmonic_ge_log (a n : ℕ) :
    log (((a + n + 1 : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ)) ≤
      ∑ i ∈ Finset.Ico a (a + n), (1 : ℝ) / ((i : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
    have hpos1 : (0 : ℝ) < ((a + n + 1 : ℕ) : ℝ) := by positivity
    have hpos2 : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by positivity
    have hsplit : log (((a + n + 1 + 1 : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ)) =
        log (((a + n + 1 : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ)) +
          log (((a + n + 2 : ℕ) : ℝ) / ((a + n + 1 : ℕ) : ℝ)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    have hstep : log (((a + n + 2 : ℕ) : ℝ) / ((a + n + 1 : ℕ) : ℝ)) ≤
        1 / (((a + n : ℕ) : ℝ) + 1) := by
      refine le_trans (Real.log_le_sub_one_of_pos (by positivity)) (le_of_eq ?_)
      field_simp
      push_cast; ring
    rw [hsplit]
    linarith

/-- One dyadic block in the proof of Corollary 2.2: if `2^{i+1}` is past the threshold of
Lemma 2.1, then `∑_{2^i < p ≤ 2^{i+1}} 1/p ≥ 1/(7 (i+1) log 2)`. -/
lemma dyadic_block {x0 : ℝ} (hx0 : ∀ x ≥ x0, x / (7 * log x) ≤ ((primesIn ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ))
    (i : ℕ) (hi : x0 ≤ (2 : ℝ) ^ (i + 1)) :
    1 / (7 * ((i : ℝ) + 1) * log 2) ≤ ∑ p ∈ primesIn (2 ^ i) (2 ^ (i + 1)), (1 : ℝ) / p := by
  have h := hx0 _ hi
  have hfl1 : ⌊(2 : ℝ) ^ (i + 1) / 2⌋₊ = 2 ^ i := by
    rw [pow_succ, mul_div_assoc, div_self (by norm_num), mul_one]
    exact_mod_cast Nat.floor_natCast (2 ^ i)
  have hfl2 : ⌊(2 : ℝ) ^ (i + 1)⌋₊ = 2 ^ (i + 1) := by exact_mod_cast Nat.floor_natCast _
  rw [hfl1, hfl2, Real.log_pow] at h
  have hsum : ((primesIn (2 ^ i) (2 ^ (i + 1))).card : ℝ) * (1 / (2 : ℝ) ^ (i + 1)) ≤
      ∑ p ∈ primesIn (2 ^ i) (2 ^ (i + 1)), (1 : ℝ) / p := by
    rw [← nsmul_eq_mul]
    apply Finset.card_nsmul_le_sum
    intro p hp
    obtain ⟨h1, h2, h3⟩ := mem_primesIn.1 hp
    apply one_div_le_one_div_of_le (by exact_mod_cast h3.pos)
    exact_mod_cast h2
  refine le_trans ?_ hsum
  have h2pos : (0 : ℝ) < 2 ^ (i + 1) := by positivity
  have hl2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  calc 1 / (7 * ((i : ℝ) + 1) * log 2)
      = (2 : ℝ) ^ (i + 1) / (7 * (((i + 1 : ℕ) : ℝ) * log 2)) * (1 / (2 : ℝ) ^ (i + 1)) := by
        push_cast; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right h (by positivity)

/-- **Corollary 2.2**: for all sufficiently large `y`, `∑_{y^8 < p ≤ y^9} 1/p ≥ c_U = 1/50`. -/
theorem cor_mertens (hR : RamanujanInequality) : ∃ y0 : ℕ, ∀ y ≥ y0,
    (1 : ℝ) / 50 ≤ ∑ p ∈ primesIn (y ^ 8) (y ^ 9), (1 : ℝ) / p := by
  obtain ⟨x0, hx0⟩ := lem_cheb hR
  set K0 : ℕ := max 75 ⌈x0⌉₊ with hK0
  refine ⟨2 ^ K0, fun y hy => ?_⟩
  have hy0 : y ≠ 0 := by have := Nat.one_le_two_pow (n := K0); omega
  set k := Nat.log 2 y with hk
  have hkK : K0 ≤ k := (Nat.le_log_iff_pow_le (by norm_num) hy0).2 hy
  have hk75 : 75 ≤ k := le_trans (le_max_left _ _) hkK
  have hkx : ⌈x0⌉₊ ≤ k := le_trans (le_max_right _ _) hkK
  have hlo : 2 ^ k ≤ y := Nat.pow_log_le_self 2 hy0
  have hhi : y < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) y
  -- the blocks `(2^i, 2^{i+1}]`, `8k+8 ≤ i < 9k`, lie inside `(y^8, y^9]`
  have hsub : (Finset.Ico (8 * k + 8) (9 * k)).biUnion
      (fun i => primesIn (2 ^ i) (2 ^ (i + 1))) ⊆ primesIn (y ^ 8) (y ^ 9) := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.1 hp
    obtain ⟨h1, h2, h3⟩ := mem_primesIn.1 hpi
    rw [Finset.mem_Ico] at hi
    refine mem_primesIn.2 ⟨?_, ?_, h3⟩
    · calc y ^ 8 < (2 ^ (k + 1)) ^ 8 := Nat.pow_lt_pow_left hhi (by norm_num)
        _ = 2 ^ (8 * k + 8) := by rw [← pow_mul]; ring_nf
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi.1
        _ < p := h1
    · calc p ≤ 2 ^ (i + 1) := h2
        _ ≤ 2 ^ (9 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (2 ^ k) ^ 9 := by rw [← pow_mul]; ring_nf
        _ ≤ y ^ 9 := Nat.pow_le_pow_left hlo 9
  have hdisj : (↑(Finset.Ico (8 * k + 8) (9 * k)) : Set ℕ).PairwiseDisjoint
      (fun i => primesIn (2 ^ i) (2 ^ (i + 1))) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpi hpj
    obtain ⟨a1, a2, -⟩ := mem_primesIn.1 hpi
    obtain ⟨b1, b2, -⟩ := mem_primesIn.1 hpj
    rcases lt_or_gt_of_ne hij with h | h
    · have : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h
      omega
    · have : 2 ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
      omega
  have hl2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  -- sum of the block bounds
  have hblocks : (1 / (7 * log 2)) * ∑ i ∈ Finset.Ico (8 * k + 8) (9 * k), (1 : ℝ) / ((i : ℝ) + 1)
      ≤ ∑ p ∈ primesIn (y ^ 8) (y ^ 9), (1 : ℝ) / p := by
    rw [Finset.mul_sum]
    calc ∑ i ∈ Finset.Ico (8 * k + 8) (9 * k), 1 / (7 * log 2) * (1 / ((i : ℝ) + 1))
        ≤ ∑ i ∈ Finset.Ico (8 * k + 8) (9 * k),
            ∑ p ∈ primesIn (2 ^ i) (2 ^ (i + 1)), (1 : ℝ) / p := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_Ico] at hi
          have hx : x0 ≤ (2 : ℝ) ^ (i + 1) := by
            calc x0 ≤ (⌈x0⌉₊ : ℝ) := Nat.le_ceil x0
              _ ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
              _ ≤ ((2 ^ (i + 1) : ℕ) : ℝ) := by exact_mod_cast (Nat.lt_two_pow_self).le
              _ = (2 : ℝ) ^ (i + 1) := by push_cast; ring
          have := dyadic_block hx0 i hx
          calc 1 / (7 * log 2) * (1 / ((i : ℝ) + 1)) = 1 / (7 * ((i : ℝ) + 1) * log 2) := by
                field_simp
            _ ≤ _ := this
      _ = ∑ p ∈ (Finset.Ico (8 * k + 8) (9 * k)).biUnion
            (fun i => primesIn (2 ^ i) (2 ^ (i + 1))), (1 : ℝ) / p := (Finset.sum_biUnion hdisj).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  -- the harmonic sum is at least `log((9k+1)/(8k+9)) ≥ log 1.11 ≥ (7/50) log 2`
  have hharm := harmonic_ge_log (8 * k + 8) (k - 8)
  have e1 : 8 * k + 8 + (k - 8) = 9 * k := by omega
  rw [e1] at hharm
  have hratio : (1.11 : ℝ) ≤ ((9 * k + 1 : ℕ) : ℝ) / ((8 * k + 8 + 1 : ℕ) : ℝ) := by
    rw [le_div_iff₀ (by positivity)]
    have : (75 : ℝ) ≤ k := by exact_mod_cast hk75
    push_cast; linarith
  have hlog111 : 7 * log 2 / 50 ≤ log (1.11 : ℝ) := by
    have h1 : log ((2 : ℝ) ^ 7) ≤ log ((1.11 : ℝ) ^ 50) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    linarith
  have hlogr := Real.log_le_log (by norm_num) hratio
  have hH : 7 * log 2 / 50 ≤ ∑ i ∈ Finset.Ico (8 * k + 8) (9 * k), (1 : ℝ) / ((i : ℝ) + 1) := by
    linarith
  calc (1 : ℝ) / 50 = (1 / (7 * log 2)) * (7 * log 2 / 50) := by field_simp
    _ ≤ (1 / (7 * log 2)) * ∑ i ∈ Finset.Ico (8 * k + 8) (9 * k), (1 : ℝ) / ((i : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hH (by positivity)
    _ ≤ _ := hblocks

end Erdos306
