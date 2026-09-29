/-
§2 of the paper: two bounds for primes.

* `lem_cheb_erdos`, `lem_cheb` — Lemma 2.1 (Chebyshev-type bounds); the lower bound is proved
  here by Erdős' central-binomial argument (`centralBinom_le_primesIn`) instead of citing
  Ramanujan's inequality;
* `cor_mertens`                — Corollary 2.2 (the large side carries reciprocal mass `≥ 1/50`).
-/
import Erdos306.Basic

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

/-- Erdős' bound on the central binomial coefficient, without the Bertrand hypothesis:
`C(2n, n) ≤ (2n)^{⌊√(2n)⌋} · 4^{⌊2n/3⌋} · (2n)^{#(primes in (n, 2n])}`. -/
theorem centralBinom_le_primesIn (n : ℕ) (n_large : 2 < n) :
    Nat.centralBinom n ≤
      (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) * (2 * n) ^ (primesIn n (2 * n)).card := by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_large
  have n2_pos : 1 ≤ 2 * n := mul_pos (zero_lt_two' ℕ) n_pos
  set f : ℕ → ℕ := fun x => x ^ n.centralBinom.factorization x with hf
  have hsplit : Nat.centralBinom n = (∏ p ∈ Finset.range (2 * n / 3 + 1), f p) *
      ∏ p ∈ Finset.Ico (2 * n / 3 + 1) (2 * n + 1), f p := by
    rw [Finset.prod_range_mul_prod_Ico _ (by omega)]
    exact n.prod_pow_factorization_centralBinom.symm
  rw [hsplit]
  apply mul_le_mul'
  · -- the small primes, exactly as in Mathlib's `centralBinom_le_of_no_bertrand_prime`
    let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
    have : ∏ x ∈ S, f x = ∏ x ∈ Finset.range (2 * n / 3 + 1), f x := by
      refine Finset.prod_filter_of_ne fun p _ h => ?_
      contrapose! h; dsimp only [f]
      rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom h, _root_.pow_zero]
    rw [← this, ← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt (2 * n))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ 2 * n)).trans ?_
      · exact Nat.pow_factorization_choose_le (mul_pos two_pos n_pos)
      have : (Finset.Icc 1 (Nat.sqrt (2 * n))).card = Nat.sqrt (2 * n) := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]
      rw [Finset.prod_const]
      refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans this.le)
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
    · refine le_trans ?_ (primorial_le_4_pow (2 * n / 3))
      refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
        refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp <| not_le.1 h2)
      refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
      exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le
  · -- the primes above `2n/3`: those `≤ n` do not divide `C(2n, n)`; the rest lie in `(n, 2n]`
    have hsub : ∏ p ∈ Finset.Ico (2 * n / 3 + 1) (2 * n + 1), f p =
        ∏ p ∈ primesIn n (2 * n), f p := by
      symm
      apply Finset.prod_subset
      · intro p hp
        obtain ⟨h1, h2, -⟩ := mem_primesIn.1 hp
        rw [Finset.mem_Ico]; omega
      · intro p hp hp'
        rw [Finset.mem_Ico] at hp
        dsimp only [f]
        by_cases hpr : p.Prime
        · have hpn : p ≤ n := by
            by_contra h
            exact hp' (mem_primesIn.2 ⟨by omega, by omega, hpr⟩)
          rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul n_large hpn (by omega),
            _root_.pow_zero]
        · rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom hpr, _root_.pow_zero]
    rw [hsub, ← Finset.prod_const]
    exact Finset.prod_le_prod' fun p _ => Nat.pow_factorization_choose_le (mul_pos two_pos n_pos)

/-- Logarithmic form: `#(primes in (n, 2n]) · log(2n) ≥ (n log 4)/3 − log(2n+1) − √(2n) log(2n)`. -/
theorem primesIn_log_lower (n : ℕ) (n_large : 2 < n) :
    (n : ℝ) * log 4 / 3 - log (2 * n + 1) - √(2 * n : ℝ) * log (2 * n) ≤
      ((primesIn n (2 * n)).card : ℝ) * log (2 * n) := by
  have h4 := Nat.four_pow_le_two_mul_add_one_mul_central_binom n
  have hc := centralBinom_le_primesIn n n_large
  rw [← Nat.centralBinom_eq_two_mul_choose] at h4
  have key : (4 : ℝ) ^ n ≤ (2 * n + 1) *
      ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) * (2 * n) ^ (primesIn n (2 * n)).card) := by
    have := h4.trans (Nat.mul_le_mul_left _ hc)
    exact_mod_cast this
  have hn : (1 : ℝ) ≤ 2 * n := by norm_cast; omega
  have hl2n : 0 ≤ log (2 * n : ℝ) := log_nonneg hn
  have hlog := Real.log_le_log (by positivity) key
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow] at hlog
  have hsq : ((Nat.sqrt (2 * n) : ℕ) : ℝ) ≤ √(2 * n : ℝ) := by
    have := @Real.nat_sqrt_le_real_sqrt (2 * n); push_cast at this; exact this
  have hdiv : (((2 * n / 3 : ℕ) : ℝ)) ≤ 2 * n / 3 := by
    have := (Nat.cast_div_le (α := ℝ) (m := 2 * n) (n := 3)); push_cast at this; exact this
  have hl4 : 0 ≤ log (4 : ℝ) := log_nonneg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hsq hl2n, mul_le_mul_of_nonneg_right hdiv hl4]

/-- **Lemma 2.1, second part**: for all sufficiently large real `x`,
`x / (7 log x) ≤ π(x) - π(x/2)`, i.e. there are at least `x/(7 log x)` primes in `(x/2, x]`.
The paper derives this from Ramanujan's inequality; here it is proved for `x ≥ 10^8` from
`primesIn_log_lower`, which is all the paper uses. -/
theorem lem_cheb : ∃ x0 : ℝ, ∀ x ≥ x0,
    x / (7 * log x) ≤ ((primesIn ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) := by
  refine ⟨100 ^ 4, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) ≤ x := le_trans (by positivity) hx
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hlog : 0 < log x := Real.log_pos hx1
  set n := ⌊x / 2⌋₊ with hn_def
  have hn1 : x / 2 - 1 < n := Nat.sub_one_lt_floor _
  have hn2 : (n : ℝ) ≤ x / 2 := Nat.floor_le (by positivity)
  have hn3 : 2 < n := by
    have : (2 : ℝ) < n := by linarith
    exact_mod_cast this
  -- the primes of `(n, 2n]` lie in `(x/2, x]`
  have hsub : primesIn n (2 * n) ⊆ primesIn ⌊x / 2⌋₊ ⌊x⌋₊ := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := mem_primesIn.1 hp
    refine mem_primesIn.2 ⟨h1, le_trans h2 ?_, h3⟩
    apply Nat.le_floor; push_cast; linarith
  have hcard : ((primesIn n (2 * n)).card : ℝ) ≤ ((primesIn ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hmain := primesIn_log_lower n hn3
  -- `r = x^{1/4}`, so that `log x ≤ 4r` and `√x = r²`
  set s := √x with hs
  set r := √s with hr
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hss : s * s = x := Real.mul_self_sqrt hx0
  have hrr : r * r = s := Real.mul_self_sqrt hs0
  have hr100 : 100 ≤ r := by
    have h1 : (100 : ℝ) ^ 2 ≤ s := by
      rw [hs, show ((100 : ℝ) ^ 2) = √((100 ^ 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    rw [hr, show (100 : ℝ) = √(100 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt h1
  have hrpos : 0 < r := by linarith
  have hlogx : log x ≤ 4 * r := by
    have : log x = 4 * log r := by
      rw [← hss, ← hrr, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]; ring
    rw [this]; nlinarith [Real.log_le_sub_one_of_pos hrpos]
  have h2n_pos : (0 : ℝ) < 2 * n := by positivity
  have h2n_le : (2 * n : ℝ) ≤ x := by linarith
  have hlog2n : log (2 * n : ℝ) ≤ log x := Real.log_le_log h2n_pos h2n_le
  have hlog2n0 : 0 ≤ log (2 * n : ℝ) := log_nonneg (by linarith)
  have hsqrt2n : √(2 * n : ℝ) ≤ s := Real.sqrt_le_sqrt h2n_le
  have hlog2n1 : log (2 * n + 1 : ℝ) ≤ 1 + 4 * r := by
    have h := Real.log_le_log (by positivity) (show (2 * n + 1 : ℝ) ≤ 2 * x by linarith)
    rw [Real.log_mul (by norm_num) (by positivity)] at h
    have : log (2 : ℝ) < 1 := by
      have := Real.log_two_lt_d9; norm_num at this; linarith
    linarith
  have hl4 : 1.38 < log (4 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have hk0 : (0 : ℝ) ≤ (primesIn n (2 * n)).card := by positivity
  -- lower bound on `k log x`
  have hklog : (n : ℝ) * log 4 / 3 - (1 + 4 * r) - s * (4 * r) ≤
      ((primesIn n (2 * n)).card : ℝ) * log x := by
    have e1 : √(2 * n : ℝ) * log (2 * n) ≤ s * (4 * r) :=
      mul_le_mul hsqrt2n (hlog2n.trans hlogx) hlog2n0 hs0
    have e2 : ((primesIn n (2 * n)).card : ℝ) * log (2 * n) ≤
        ((primesIn n (2 * n)).card : ℝ) * log x := mul_le_mul_of_nonneg_left hlog2n hk0
    linarith
  rw [div_le_iff₀ (by positivity)]
  have hxr : x = r * r * (r * r) := by rw [hrr, hss]
  have hnl : (x / 2 - 1) * 1.38 ≤ (n : ℝ) * log 4 := by
    apply mul_le_mul (le_of_lt hn1) (le_of_lt hl4) (by norm_num) (by positivity)
  have hcl := mul_le_mul_of_nonneg_right hcard hlog.le
  rw [← hrr] at hklog
  nlinarith [mul_pos hrpos hrpos, mul_pos (mul_pos hrpos hrpos) hrpos]

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
theorem cor_mertens : ∃ y0 : ℕ, ∀ y ≥ y0,
    (1 : ℝ) / 50 ≤ ∑ p ∈ primesIn (y ^ 8) (y ^ 9), (1 : ℝ) / p := by
  obtain ⟨x0, hx0⟩ := lem_cheb
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
