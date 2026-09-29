/-
All "for `y` sufficiently large" statements of the paper, collected: every field of `Large τ y`
holds for all large `y`.
-/
import Erdos306.Construction

namespace Erdos306

open Real Finset

/-- The bound for `ε` stated in §8.1: `ε ≤ exp(-y²/(2·10⁷ log³ y))` (from eq. (1)). -/
lemma eps_le {y : ℕ} (hy : 3 ≤ y) (hW : (y : ℝ) ^ 2 / (8 * log y) ≤ (Wset y).card) :
    eps y ≤ exp (-((y : ℝ) ^ 2 / (2 * 10 ^ 7 * log y ^ 3))) := by
  unfold eps delta
  apply Real.exp_le_exp.2
  have hlog : 0 < log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hy2 : (0 : ℝ) ≤ (y : ℝ) ^ 2 := by positivity
  have hdelta : (1 / (400 * log (y : ℝ))) ^ 2 / 8 = 1 / (1280000 * log y ^ 2) := by
    field_simp; ring
  have h1 : (y : ℝ) ^ 2 / (2 * 10 ^ 7 * log y ^ 3) ≤
      (y : ℝ) ^ 2 / (8 * log y) * (1 / (1280000 * log y ^ 2)) := by
    rw [div_mul_div_comm, mul_one]
    apply div_le_div_of_nonneg_left hy2 (by positivity)
    nlinarith [pow_pos hlog 3]
  have h2 : (y : ℝ) ^ 2 / (8 * log y) * (1 / (1280000 * log y ^ 2)) ≤
      (Wset y).card * (1 / (1280000 * log y ^ 2)) :=
    mul_le_mul_of_nonneg_right hW (by positivity)
  rw [mul_div_assoc, hdelta]
  linarith

/-- A `y`-uniform version of the bounds eq. (1) for `H_V`:
`½ ≤ H_V ≤ 3/2 + ∑_{r ∈ B} 1/r` for every `y ≥ 1` (using `∑_{w ∈ W} 1/w ≤ |W|/y² ≤ 1`). -/
lemma HV_bounds_uniform (τ : ℚ) {y : ℕ} (hy : 1 ≤ y) :
    1 / 2 ≤ HV τ y ∧ HV τ y ≤ 3 / 2 + ∑ r ∈ Bset τ, (1 : ℝ) / r := by
  have hnn : ∀ s : Finset ℕ, 0 ≤ ∑ i ∈ s, (1 : ℝ) / i := fun s => by positivity
  constructor
  · unfold HV
    have := Finset.single_le_sum (f := fun v : ℕ => (1 : ℝ) / v)
      (fun i _ => by positivity) (two_mem_Vset (τ := τ) (y := y))
    simpa using this
  · -- `∑_{w ∈ W} 1/w ≤ 1`
    have hW : ∑ w ∈ Wset y, (1 : ℝ) / w ≤ 1 := by
      have hy2 : (0 : ℝ) < (y : ℝ) ^ 2 := by positivity
      calc ∑ w ∈ Wset y, (1 : ℝ) / w ≤ ∑ w ∈ Wset y, (1 : ℝ) / (y : ℝ) ^ 2 := by
            apply Finset.sum_le_sum
            intro w hw
            have := (mem_Wset.1 hw).1
            apply one_div_le_one_div_of_le hy2
            exact_mod_cast this.le
        _ = (Wset y).card / (y : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ 1 := by
            rw [div_le_one hy2]
            have : (Wset y).card ≤ y ^ 2 := by
              calc (Wset y).card ≤ (Finset.Ioc (y ^ 2) (2 * y ^ 2)).card :=
                    Finset.card_filter_le _ _
                _ = y ^ 2 := by simp; omega
            exact_mod_cast this
    have hunion : ∑ v ∈ Bset τ ∪ Wset y, (1 : ℝ) / v ≤
        ∑ v ∈ Bset τ, (1 : ℝ) / v + ∑ v ∈ Wset y, (1 : ℝ) / v := by
      rw [← Finset.sum_union_inter]
      linarith [hnn (Bset τ ∩ Wset y)]
    have hins : HV τ y ≤ 1 / 2 + ∑ v ∈ Bset τ ∪ Wset y, (1 : ℝ) / v := by
      unfold HV Vset
      by_cases h2 : 2 ∈ Bset τ ∪ Wset y
      · rw [Finset.insert_eq_of_mem h2]; linarith
      · rw [Finset.sum_insert h2]; norm_num
    linarith

/-- `y^30 ε ≤ 1` for large `y` (the only place where the super-polynomial decay of `ε`,
`ε ≤ exp(-y²/(2·10⁷ log³ y))`, is used). -/
lemma y30_eps_le {y : ℕ} (hy : 2 * 10 ^ 11 ≤ y)
    (hW : (y : ℝ) ^ 2 / (8 * log y) ≤ (Wset y).card) : (y : ℝ) ^ 30 * eps y ≤ 1 := by
  have hy3 : 3 ≤ y := by omega
  have hyR : (2 * 10 ^ 11 : ℝ) ≤ y := by exact_mod_cast hy
  have hypos : (0 : ℝ) < y := by linarith
  have hlog : 0 < log (y : ℝ) := Real.log_pos (by linarith)
  -- `log y ≤ 4 y^{1/4}`, hence `log⁴ y ≤ 256 y`
  have hl4 : log (y : ℝ) ^ 4 ≤ 256 * y := by
    have h1 := Real.log_le_rpow_div hypos.le (by norm_num : (0 : ℝ) < 1 / 4)
    have h2 : ((y : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = y := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hypos.le]; norm_num
    calc log (y : ℝ) ^ 4 ≤ ((y : ℝ) ^ (1 / 4 : ℝ) / (1 / 4)) ^ 4 :=
          pow_le_pow_left₀ hlog.le h1 4
      _ = 256 * ((y : ℝ) ^ (1 / 4 : ℝ)) ^ 4 := by ring
      _ = 256 * y := by rw [h2]
  -- hence `30 log y ≤ y²/(2·10⁷ log³ y)`
  have hkey : 30 * log (y : ℝ) ≤ (y : ℝ) ^ 2 / (2 * 10 ^ 7 * log y ^ 3) := by
    rw [le_div_iff₀ (by positivity)]
    have : 30 * log (y : ℝ) * (2 * 10 ^ 7 * log y ^ 3) = 6 * 10 ^ 8 * log y ^ 4 := by ring
    rw [this]
    nlinarith
  have he := eps_le hy3 hW
  have hy30 : (y : ℝ) ^ 30 = exp (30 * log y) := by
    rw [show (30 : ℝ) = ((30 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hypos]
  rw [hy30]
  calc exp (30 * log y) * eps y
      ≤ exp (30 * log y) * exp (-((y : ℝ) ^ 2 / (2 * 10 ^ 7 * log y ^ 3))) :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = exp (30 * log y - (y : ℝ) ^ 2 / (2 * 10 ^ 7 * log y ^ 3)) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ exp 0 := Real.exp_le_exp.2 (by linarith)
    _ = 1 := Real.exp_zero

/-- `|W| ≥ y²/(8 log y)` for large `y` (eq. (1), from Lemma 2.1 with `x = 2y²`). -/
lemma card_W_eventually : ∃ y0 : ℕ, ∀ y ≥ y0, (y : ℝ) ^ 2 / (8 * log y) ≤ (Wset y).card := by
  obtain ⟨x0, hx0⟩ := lem_cheb
  refine ⟨max 12 ⌈x0⌉₊, fun y hy => ?_⟩
  have hy12 : 12 ≤ y := le_trans (le_max_left _ _) hy
  have hyx : ⌈x0⌉₊ ≤ y := le_trans (le_max_right _ _) hy
  have hyR : (12 : ℝ) ≤ y := by exact_mod_cast hy12
  have hx : x0 ≤ 2 * (y : ℝ) ^ 2 := by
    calc x0 ≤ (⌈x0⌉₊ : ℝ) := Nat.le_ceil x0
      _ ≤ y := by exact_mod_cast hyx
      _ ≤ 2 * (y : ℝ) ^ 2 := by nlinarith
  have h := hx0 _ hx
  have hf1 : ⌊2 * (y : ℝ) ^ 2 / 2⌋₊ = y ^ 2 := by
    rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    exact_mod_cast Nat.floor_natCast (y ^ 2)
  have hf2 : ⌊2 * (y : ℝ) ^ 2⌋₊ = 2 * y ^ 2 := by exact_mod_cast Nat.floor_natCast (2 * y ^ 2)
  rw [hf1, hf2] at h
  refine le_trans ?_ h
  have hlog : 0 < log (y : ℝ) := Real.log_pos (by linarith)
  have hlog2 : log (2 * (y : ℝ) ^ 2) = log 2 + 2 * log y := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  -- `7 log 2 ≤ 2 log y` since `2^7 ≤ y²`
  have h7 : 7 * log (2 : ℝ) ≤ 2 * log y := by
    have : log ((2 : ℝ) ^ 7) ≤ log ((y : ℝ) ^ 2) := Real.log_le_log (by norm_num) (by nlinarith)
    rw [Real.log_pow, Real.log_pow] at this; push_cast at this; linarith
  have hl2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [hlog2, div_le_div_iff₀ (by positivity) (by positivity)]
  have hy2 : (0 : ℝ) ≤ (y : ℝ) ^ 2 := by positivity
  nlinarith

/-- Numerics for Proposition 9.1, case III (one column):
`e^{-2δ_a²} + y^9 ε ≤ e^{-δ_a²}`, since `e^{-x} - e^{-2x} ≥ x/2` and `y^9 ε ≤ 1/(128 y⁴)`. -/
lemma colIII_numeric {y : ℕ} (hy : 128 ≤ y) (heps : (y : ℝ) ^ 30 * eps y ≤ 1) :
    exp (-2 * deltaA y ^ 2) + (y : ℝ) ^ 9 * eps y ≤ exp (-(deltaA y ^ 2)) := by
  have hyR : (128 : ℝ) ≤ y := by exact_mod_cast hy
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  set x := deltaA y ^ 2 with hx
  have hxy : x = 1 / (64 * (y : ℝ) ^ 4) := by rw [hx]; unfold deltaA; field_simp; ring
  have hx0 : 0 ≤ x := by rw [hxy]; positivity
  have hx4 : x ≤ 1 / 4 := by
    rw [hxy, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [one_le_pow₀ (n := 4) hy1]
  have hdiff : x / 2 ≤ exp (-x) - exp (-2 * x) := by
    have h1 : exp (-x) - exp (-2 * x) = exp (-2 * x) * (exp x - 1) := by
      rw [mul_sub, ← Real.exp_add]; ring_nf
    have h2 : x ≤ exp x - 1 := by linarith [Real.add_one_le_exp x]
    have h3 : 1 - 2 * x ≤ exp (-2 * x) := by linarith [Real.add_one_le_exp (-2 * x)]
    rw [h1]
    nlinarith
  have hy9 : (y : ℝ) ^ 9 * eps y ≤ x / 2 := by
    rw [hxy]
    have hy17 : (128 : ℝ) ≤ (y : ℝ) ^ 17 := le_trans hyR (le_self_pow₀ hy1 (by norm_num))
    have : (y : ℝ) ^ 9 * eps y * (128 * (y : ℝ) ^ 4) ≤ 1 := by
      calc (y : ℝ) ^ 9 * eps y * (128 * (y : ℝ) ^ 4) = 128 * ((y : ℝ) ^ 13 * eps y) := by ring
        _ ≤ (y : ℝ) ^ 17 * ((y : ℝ) ^ 13 * eps y) :=
            mul_le_mul_of_nonneg_right hy17 (by positivity)
        _ = (y : ℝ) ^ 30 * eps y := by ring
        _ ≤ 1 := heps
    rw [div_div, le_div_iff₀ (by positivity)]
    linarith
  linarith

/-- Numerics for Proposition 9.1, case II: `3y^{25} ε e^{y^{18} ε} ≤ 1/4`. -/
lemma caseII_numeric {y : ℕ} (hy : 36 ≤ y) (heps : (y : ℝ) ^ 30 * eps y ≤ 1) :
    3 * (y : ℝ) ^ 25 * eps y * exp ((y : ℝ) ^ 18 * eps y) ≤ 1 / 4 := by
  have hyR : (36 : ℝ) ≤ y := by exact_mod_cast hy
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  have hy12 : (1 : ℝ) ≤ (y : ℝ) ^ 12 := one_le_pow₀ hy1
  have h18 : (y : ℝ) ^ 18 * eps y ≤ 1 := by
    calc (y : ℝ) ^ 18 * eps y ≤ (y : ℝ) ^ 12 * ((y : ℝ) ^ 18 * eps y) :=
          le_mul_of_one_le_left (by positivity) hy12
      _ = (y : ℝ) ^ 30 * eps y := by ring
      _ ≤ 1 := heps
  have hexp : exp ((y : ℝ) ^ 18 * eps y) ≤ 3 := by
    calc exp ((y : ℝ) ^ 18 * eps y) ≤ exp 1 := Real.exp_le_exp.2 h18
      _ ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have h25 : 36 * ((y : ℝ) ^ 25 * eps y) ≤ 1 := by
    have hy5 : (36 : ℝ) ≤ (y : ℝ) ^ 5 := le_trans hyR (le_self_pow₀ hy1 (by norm_num))
    calc 36 * ((y : ℝ) ^ 25 * eps y) ≤ (y : ℝ) ^ 5 * ((y : ℝ) ^ 25 * eps y) :=
          mul_le_mul_of_nonneg_right hy5 (by positivity)
      _ = (y : ℝ) ^ 30 * eps y := by ring
      _ ≤ 1 := heps
  have hpos : 0 ≤ 3 * (y : ℝ) ^ 25 * eps y := by positivity
  calc 3 * (y : ℝ) ^ 25 * eps y * exp ((y : ℝ) ^ 18 * eps y)
      ≤ 3 * (y : ℝ) ^ 25 * eps y * 3 := mul_le_mul_of_nonneg_left hexp hpos
    _ ≤ 1 / 4 := by linarith

/-- Numerics for Proposition 9.1, case III (total): with `C ≥ H_V` and `y² ≥ Q`,
`2b·16^{y²}·exp(-τy⁴/(64 H_V)) ≤ 1/4`. -/
lemma caseIII_numeric {τ : ℚ} {y : ℕ} (hτ : 0 < τ) {C : ℝ} (hHV0 : 0 < HV τ y)
    (hHVC : HV τ y ≤ C) (hy1 : (1 : ℝ) ≤ y)
    (hyQ : 64 * C * (log (8 * τ.den) + log 16) / τ ≤ (y : ℝ) ^ 2) :
    2 * (τ.den : ℝ) * 16 ^ (y ^ 2) * exp (-((τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y))) ≤ 1 / 4 := by
  have hτR : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hden1 : (1 : ℝ) ≤ τ.den := by exact_mod_cast τ.den_pos
  have hlog8b : 0 ≤ log (8 * (τ.den : ℝ)) := Real.log_nonneg (by linarith)
  have hlog16 : 0 < log (16 : ℝ) := Real.log_pos (by norm_num)
  have hC0 : 0 < C := lt_of_lt_of_le hHV0 hHVC
  have h16 : (16 : ℝ) ^ (y ^ 2) = exp ((y : ℝ) ^ 2 * log 16) := by
    rw [show ((y : ℝ) ^ 2) = ((y ^ 2 : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul,
      Real.exp_log (by norm_num)]
  have h8b : 2 * (τ.den : ℝ) = exp (log (8 * τ.den)) / 4 := by
    rw [Real.exp_log (by positivity)]; ring
  have hexp : (y : ℝ) ^ 2 * log 16 + log (8 * τ.den) ≤ (τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y) := by
    have h1 : (τ : ℝ) * (y : ℝ) ^ 4 / (64 * C) ≤ (τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    refine le_trans ?_ h1
    have hQ' : 64 * C * (log (8 * τ.den) + log 16) ≤ τ * (y : ℝ) ^ 2 := by
      rwa [div_le_iff₀ hτR, mul_comm ((y : ℝ) ^ 2)] at hyQ
    rw [le_div_iff₀ (by positivity)]
    have hy2 : (1 : ℝ) ≤ (y : ℝ) ^ 2 := one_le_pow₀ hy1
    calc ((y : ℝ) ^ 2 * log 16 + log (8 * τ.den)) * (64 * C)
        ≤ (y : ℝ) ^ 2 * (64 * C * (log (8 * τ.den) + log 16)) := by
          have e : (y : ℝ) ^ 2 * (64 * C * (log (8 * τ.den) + log 16)) -
              ((y : ℝ) ^ 2 * log 16 + log (8 * τ.den)) * (64 * C) =
              ((y : ℝ) ^ 2 - 1) * (64 * C * log (8 * τ.den)) := by ring
          have : 0 ≤ ((y : ℝ) ^ 2 - 1) * (64 * C * log (8 * τ.den)) := by
            apply mul_nonneg (by linarith); positivity
          linarith
      _ ≤ (y : ℝ) ^ 2 * (τ * (y : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hQ' (by positivity)
      _ = τ * (y : ℝ) ^ 4 := by ring
  rw [h16, h8b]
  calc exp (log (8 * τ.den)) / 4 * exp ((y : ℝ) ^ 2 * log 16) *
        exp (-((τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y)))
      = exp ((y : ℝ) ^ 2 * log 16 + log (8 * τ.den) -
          (τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y)) / 4 := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]; ring
    _ ≤ exp 0 / 4 := by gcongr; linarith
    _ = 1 / 4 := by rw [Real.exp_zero]

/-- Numerics for Lemma 8.2 and Proposition 9.1 (case II): `800 log y ≤ y²` gives
`y²/(20 log y) + 10 ≤ y²/(16 log y)` and `y^{-3} ≤ δ/2`. -/
lemma count_phase_numeric {y : ℕ} (hy : 800 ≤ y) :
    (y : ℝ) ^ 2 / (20 * log y) + 10 ≤ (y : ℝ) ^ 2 / (16 * log y) ∧
      1 / (y : ℝ) ^ 3 ≤ delta y / 2 := by
  have hyR : (800 : ℝ) ≤ y := by exact_mod_cast hy
  have hypos : (0 : ℝ) < y := by linarith
  have hlog : 0 < log (y : ℝ) := Real.log_pos (by linarith)
  have hlogy : log (y : ℝ) ≤ y := le_trans (Real.log_le_sub_one_of_pos hypos) (by linarith)
  have h800 : 800 * log (y : ℝ) ≤ (y : ℝ) ^ 2 := by nlinarith
  constructor
  · have e : (y : ℝ) ^ 2 / (16 * log y) - (y : ℝ) ^ 2 / (20 * log y) =
        (y : ℝ) ^ 2 / (80 * log y) := by
      field_simp; ring
    have : 10 ≤ (y : ℝ) ^ 2 / (80 * log y) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  · unfold delta
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- All the "sufficiently large `y`" conditions hold simultaneously for large `y`. -/
theorem eventually_large {τ : ℚ} (h0 : 0 < τ) :
    ∃ y0 : ℕ, ∀ y ≥ y0, Large τ y := by
  obtain ⟨yW, hyW⟩ := card_W_eventually
  obtain ⟨yM, hyM⟩ := cor_mertens
  set C : ℝ := 3 / 2 + ∑ r ∈ Bset τ, (1 : ℝ) / r with hC
  have hτR : (0 : ℝ) < τ := by exact_mod_cast h0
  set Q : ℝ := 64 * C * (log (8 * τ.den) + log 16) / τ with hQ
  refine ⟨max (max yW yM) (max (2 * 10 ^ 11) (max (τ.den + 1)
    (⌈C / τ⌉₊ + ⌈2 * C⌉₊ + ⌈Q⌉₊ + 1))), fun y hy => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hy
  obtain ⟨⟨hyW', hyM'⟩, hbig, hden, hy1'⟩ := hy
  have hyR : (2 * 10 ^ 11 : ℝ) ≤ y := by exact_mod_cast hbig
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hsum : (⌈C / τ⌉₊ : ℝ) + ⌈2 * C⌉₊ + ⌈Q⌉₊ + 1 ≤ y := by exact_mod_cast hy1'
  have c1 := Nat.le_ceil (C / τ)
  have c2 := Nat.le_ceil (2 * C)
  have c3 := Nat.le_ceil Q
  have n1 : (0 : ℝ) ≤ ⌈C / τ⌉₊ := Nat.cast_nonneg _
  have n2 : (0 : ℝ) ≤ ⌈2 * C⌉₊ := Nat.cast_nonneg _
  have n3 : (0 : ℝ) ≤ ⌈Q⌉₊ := Nat.cast_nonneg _
  have hyC : C / τ ≤ y := by linarith
  have hy2C : 2 * C < y := by linarith
  have hyQ : Q ≤ (y : ℝ) ^ 2 := le_trans (by linarith) (le_self_pow₀ hy1 (by norm_num))
  have hHV := HV_bounds_uniform τ (y := y) (by omega)
  have hHVpos : 0 < HV τ y := by linarith [hHV.1]
  have hW := hyW y hyW'
  have heps := y30_eps_le hbig hW
  have hcp := count_phase_numeric (y := y) (by omega)
  refine
    { y_ge := by omega
      B_lt := ?_
      card_W := hW
      mertens := hyM y hyM'
      tune := ?_
      major := ?_
      count := hcp.1
      phase := hcp.2
      colIII := colIII_numeric (by omega) heps
      caseIII := caseIII_numeric h0 hHVpos hHV.2 hy1 hyQ
      caseII := caseII_numeric (by omega) heps }
  · intro r hr
    have hr' := Nat.le_of_dvd τ.den_pos (Nat.dvd_of_mem_primeFactors hr)
    omega
  · -- `H_V/(2y^8) < τ/2`: `H_V ≤ C ≤ τ y < τ y^8`
    have hy8 : (y : ℝ) < (y : ℝ) ^ 8 := by
      have : (y : ℝ) ^ 1 < (y : ℝ) ^ 8 := pow_lt_pow_right₀ (by linarith) (by norm_num)
      simpa using this
    have hCy : C ≤ τ * y := by rwa [div_le_iff₀ hτR, mul_comm] at hyC
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hHV.2]
  · -- `2 H_V < y`
    linarith [hHV.2]

end Erdos306
