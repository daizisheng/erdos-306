/-
§4 of the paper: the construction `V = {2} ∪ B ∪ W`, `U = U(Y)`, the tuning lemma, and the
reduction of Theorem 3.1 to Proposition 4.2 (a congruence mod 1 forces equality).

Conventions.  The target is a rational `τ` (the paper's `a/b`, so `b = τ.den`); `y` is a natural
number (the paper allows real `y`; natural `y` suffices and makes `y^7` an integer).
Edges `vu` of the complete bipartite graph `V × U` are pairs `(v, u) : ℕ × ℕ`.
The endpoint `Y` is a natural number with `y^8 ≤ Y ≤ y^9` (the paper takes `Y` prime; only
the set `U(Y)` matters, and `U(Y) = U(max U(Y))`).
-/
import Erdos306.Primes

namespace Erdos306

open Real Finset

variable (τ : ℚ) (y Y : ℕ)

/-- `B`: the primes dividing `b = τ.den`. -/
def Bset : Finset ℕ := τ.den.primeFactors

/-- `W = {w prime : y^2 < w ≤ 2y^2}`: the test primes. -/
def Wset : Finset ℕ := primesIn (y ^ 2) (2 * y ^ 2)

/-- The small side `V = {2} ∪ B ∪ W`. -/
def Vset : Finset ℕ := insert 2 (Bset τ ∪ Wset y)

/-- The large side `U = U(Y) = {u prime : y^8 < u ≤ Y}`. -/
def Uset : Finset ℕ := primesIn (y ^ 8) Y

/-- `H_V = ∑_{v ∈ V} 1/v`. -/
noncomputable def HV : ℝ := ∑ v ∈ Vset τ y, (1 : ℝ) / v

/-- The edge set `A = A(Y) = V × U`. -/
def Aset : Finset (ℕ × ℕ) := Vset τ y ×ˢ Uset y Y

/-- `μ(Y) = ½ ∑_{(v,u) ∈ A} 1/(uv)`: half the total mass of `A`. -/
noncomputable def mu : ℝ := (1 / 2) * ∑ p ∈ Aset τ y Y, (1 : ℝ) / (p.1 * p.2)

/-- `σ(S) = ∑_{(v,u) ∈ S} 1/(vu)` (a rational number). -/
def sigma (S : Finset (ℕ × ℕ)) : ℚ := ∑ p ∈ S, (1 : ℚ) / (p.1 * p.2)

/-- `L = ∏_{p ∈ V ∪ U} p`. -/
def Lnum : ℕ := ∏ p ∈ Vset τ y ∪ Uset y Y, p

/-- `δ = 1/(400 log y)` (paper §8.1). -/
noncomputable def delta : ℝ := 1 / (400 * log y)

/-- `ε = exp(-|W| δ² / 8)` (paper §8.1). -/
noncomputable def eps : ℝ := exp (-((Wset y).card * delta y ^ 2 / 8))

/-- `δ_a = 1/(8y²)` (paper §8.2). -/
noncomputable def deltaA : ℝ := 1 / (8 * (y : ℝ) ^ 2)

/-- All the inequalities that the paper asserts "for `y` sufficiently large (in terms of `b`)".
Each field is used at exactly the place indicated; `eventually_large` (file `Asymptotics`)
shows that they all hold for all large `y`. -/
structure Large : Prop where
  /-- a harmless lower bound on `y` -/
  y_ge : 3 ≤ y
  /-- `y > max B` (§4) -/
  B_lt : ∀ r ∈ Bset τ, r < y
  /-- eq. (1): `|W| ≥ y²/(8 log y)` -/
  card_W : (y : ℝ) ^ 2 / (8 * log y) ≤ (Wset y).card
  /-- eq. (1) / Corollary 2.2: `∑_{u ∈ U(y^9)} 1/u ≥ c_U = 1/50` -/
  mertens : (1 : ℝ) / 50 ≤ ∑ u ∈ Uset y (y ^ 9), (1 : ℝ) / u
  /-- Lemma 4.1: `H_V/(2y^8) < τ/2` -/
  tune : HV τ y / (2 * (y : ℝ) ^ 8) < τ / 2
  /-- Proposition 7.1, step 4: `y > 2 H_V` -/
  major : 2 * HV τ y < y
  /-- Lemma 8.2: `y²/(20 log y) + 10 ≤ y²/(16 log y)` -/
  count : (y : ℝ) ^ 2 / (20 * log y) + 10 ≤ (y : ℝ) ^ 2 / (16 * log y)
  /-- Proposition 9.1, case II: `y^{-3} ≤ δ/2` -/
  phase : 1 / (y : ℝ) ^ 3 ≤ delta y / 2
  /-- Proposition 9.1, case III: `e^{-2δ_a²} + Yε ≤ e^{-δ_a²}` (with `Y ≤ y^9`) -/
  colIII : exp (-2 * deltaA y ^ 2) + (y : ℝ) ^ 9 * eps y ≤ exp (-(deltaA y ^ 2))
  /-- Proposition 9.1, case III: `2b·16^{y²}·exp(-τy⁴/(64 H_V)) ≤ 1/4` -/
  caseIII : 2 * (τ.den : ℝ) * 16 ^ (y ^ 2) * exp (-((τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y)))
    ≤ 1 / 4
  /-- Proposition 9.1, case II: `3y^{25} ε e^{y^{18} ε} ≤ 1/4` -/
  caseII : 3 * (y : ℝ) ^ 25 * eps y * exp ((y : ℝ) ^ 18 * eps y) ≤ 1 / 4

/-- The conclusions of the tuning lemma (Lemma 4.1) for the endpoint `Y`. -/
structure Tuned : Prop where
  lo : y ^ 8 ≤ Y
  hi : Y ≤ y ^ 9
  beta_nonpos : mu τ y Y ≤ τ
  beta_ge : (τ : ℝ) - mu τ y Y ≤ HV τ y / (2 * (y : ℝ) ^ 8)
  mu_ge : (τ : ℝ) / 2 ≤ mu τ y Y
  card_U : (τ : ℝ) * (y : ℝ) ^ 8 / HV τ y ≤ (Uset y Y).card

/-! ### Elementary facts about the construction -/

section facts

variable {τ y Y}

/-- Membership in `W`. -/
lemma mem_Wset {w : ℕ} : w ∈ Wset y ↔ y ^ 2 < w ∧ w ≤ 2 * y ^ 2 ∧ w.Prime := mem_primesIn

/-- Membership in `U(Y)`. -/
lemma mem_Uset {u : ℕ} : u ∈ Uset y Y ↔ y ^ 8 < u ∧ u ≤ Y ∧ u.Prime := mem_primesIn

/-- Membership in `V = {2} ∪ B ∪ W`. -/
lemma mem_Vset {v : ℕ} : v ∈ Vset τ y ↔ v = 2 ∨ v ∈ Bset τ ∨ v ∈ Wset y := by
  simp [Vset]

/-- Membership in `A = V × U`. -/
lemma mem_Aset {p : ℕ × ℕ} : p ∈ Aset τ y Y ↔ p.1 ∈ Vset τ y ∧ p.2 ∈ Uset y Y := by
  simp [Aset]

/-- Every element of `V` is prime. -/
lemma prime_of_mem_Vset {v : ℕ} (hv : v ∈ Vset τ y) : v.Prime := by
  rcases mem_Vset.1 hv with h | h | h
  · subst h; exact Nat.prime_two
  · exact Nat.prime_of_mem_primeFactors h
  · exact (mem_Wset.1 h).2.2

/-- Every element of `U` is prime. -/
lemma prime_of_mem_Uset {u : ℕ} (hu : u ∈ Uset y Y) : u.Prime := (mem_Uset.1 hu).2.2

/-- `2 ∈ V`. -/
lemma two_mem_Vset : 2 ∈ Vset τ y := by simp [Vset]

/-- `W ⊆ V`. -/
lemma Wset_subset_Vset : Wset y ⊆ Vset τ y := by
  intro w hw; simp [Vset, hw]

/-- Every `v ∈ V` satisfies `2 ≤ v ≤ 2y²`. -/
lemma le_of_mem_Vset (hL : Large τ y) {v : ℕ} (hv : v ∈ Vset τ y) : 2 ≤ v ∧ v ≤ 2 * y ^ 2 := by
  refine ⟨(prime_of_mem_Vset hv).two_le, ?_⟩
  have hy := hL.y_ge
  have hyy : y ≤ y ^ 2 := Nat.le_self_pow (by norm_num) y
  rcases mem_Vset.1 hv with h | h | h
  · omega
  · have := hL.B_lt v h; omega
  · exact (mem_Wset.1 h).2.1

/-- Every `u ∈ U(Y)` satisfies `y^8 < u ≤ Y`. -/
lemma bounds_of_mem_Uset {u : ℕ} (hu : u ∈ Uset y Y) : y ^ 8 < u ∧ u ≤ Y :=
  ⟨(mem_Uset.1 hu).1, (mem_Uset.1 hu).2.1⟩

/-- `V` and `U` are disjoint (they live at different scales). -/
lemma two_y_sq_lt (hL : Large τ y) : 2 * y ^ 2 < y ^ 8 := by
  have hy := hL.y_ge
  have h6 : 2 < y ^ 6 := by
    calc 2 < 3 ^ 6 := by norm_num
      _ ≤ y ^ 6 := Nat.pow_le_pow_left hy 6
  have : y ^ 8 = y ^ 2 * y ^ 6 := by ring
  rw [this]
  have : 0 < y ^ 2 := by positivity
  nlinarith

/-- `V` and `U` are disjoint (they live at different scales, `v ≤ 2y² < y^8 < u`). -/
lemma disjoint_V_U (hL : Large τ y) : Disjoint (Vset τ y) (Uset y Y) := by
  rw [Finset.disjoint_left]
  intro v hv hu
  have h1 := (le_of_mem_Vset hL hv).2
  have h2 := (bounds_of_mem_Uset hu).1
  have := two_y_sq_lt hL
  omega

/-- `b ∣ L`: the primes of `b` are among the primes of the graph (`b` squarefree). -/
lemma den_dvd_L (hsq : Squarefree τ.den) : τ.den ∣ Lnum τ y Y := by
  have h : ∏ p ∈ Bset τ, p = τ.den := Nat.prod_primeFactors_of_squarefree hsq
  rw [← h]
  apply Finset.prod_dvd_prod_of_subset
  intro r hr
  exact Finset.mem_union_left _ (by simp [Vset, hr])

/-- every edge `vu` divides `L` -/
lemma edge_dvd_L (hL : Large τ y) {p : ℕ × ℕ} (hp : p ∈ Aset τ y Y) :
    p.1 * p.2 ∣ Lnum τ y Y := by
  obtain ⟨hv, hu⟩ := mem_Aset.1 hp
  have hne : p.1 ≠ p.2 := by
    intro h
    exact Finset.disjoint_left.1 (disjoint_V_U (Y := Y) hL) hv (h ▸ hu)
  have : ∏ x ∈ ({p.1, p.2} : Finset ℕ), x = p.1 * p.2 := Finset.prod_pair hne
  rw [← this]
  apply Finset.prod_dvd_prod_of_subset
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact Finset.mem_union_left _ hv
  · exact Finset.mem_union_right _ hu

/-- `μ = ½ H_V ∑_{u ∈ U} 1/u`. -/
lemma mu_eq : mu τ y Y = (1 / 2) * HV τ y * ∑ u ∈ Uset y Y, (1 : ℝ) / u := by
  unfold mu HV Aset
  rw [Finset.sum_product, mul_assoc, Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun u _ => ?_))
  rw [div_mul_div_comm, one_mul]

/-- eq. (1), second item: `∏_{v ∈ V} v ≤ 2 b 16^{y²}`. -/
lemma prod_V_le :
    ((∏ v ∈ Vset τ y, v : ℕ) : ℝ) ≤ 2 * τ.den * 16 ^ (y ^ 2) := by
  -- `∏_{insert 2 s} ∣ 2 ∏_s`
  have h1 : ∏ v ∈ Vset τ y, v ∣ 2 * ∏ v ∈ Bset τ ∪ Wset y, v := by
    unfold Vset
    by_cases h2 : 2 ∈ Bset τ ∪ Wset y
    · rw [Finset.insert_eq_of_mem h2]; exact Dvd.intro_left _ rfl
    · rw [Finset.prod_insert h2]
  have h2 : ∏ v ∈ Bset τ ∪ Wset y, v ∣ (∏ v ∈ Bset τ, v) * ∏ v ∈ Wset y, v := by
    rw [← Finset.prod_union_inter]; exact Dvd.intro _ rfl
  have hB : ∏ v ∈ Bset τ, v ∣ τ.den := Nat.prod_primeFactors_dvd τ.den
  have hW : ∏ v ∈ Wset y, v ∣ primorial (2 * y ^ 2) := by
    unfold primorial
    apply Finset.prod_dvd_prod_of_subset
    intro w hw
    obtain ⟨-, h2, h3⟩ := mem_Wset.1 hw
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, h3⟩
  have hprim := primorial_le_4_pow (2 * y ^ 2)
  have hden := τ.den_pos
  have hpp : 0 < primorial (2 * y ^ 2) := primorial_pos _
  have hN : ∏ v ∈ Vset τ y, v ≤ 2 * τ.den * 16 ^ (y ^ 2) := by
    have h3 : ∏ v ∈ Vset τ y, v ∣ 2 * (τ.den * primorial (2 * y ^ 2)) :=
      h1.trans (mul_dvd_mul_left 2 (h2.trans (mul_dvd_mul hB hW)))
    have h4 := Nat.le_of_dvd (by positivity) h3
    have h5 : (4 : ℕ) ^ (2 * y ^ 2) = 16 ^ (y ^ 2) := by
      rw [pow_mul]; norm_num
    calc ∏ v ∈ Vset τ y, v ≤ 2 * (τ.den * primorial (2 * y ^ 2)) := h4
      _ ≤ 2 * (τ.den * 4 ^ (2 * y ^ 2)) := by gcongr
      _ = 2 * τ.den * 16 ^ (y ^ 2) := by rw [h5]; ring
  exact_mod_cast hN

/-- eq. (1), third item: `½ ≤ H_V ≤ 3/2 + ∑_{r ∈ B} 1/r`. -/
lemma HV_bounds (hL : Large τ y) :
    1 / 2 ≤ HV τ y ∧ HV τ y ≤ 3 / 2 + ∑ r ∈ Bset τ, (1 : ℝ) / r := by
  have hnn : ∀ s : Finset ℕ, ∀ i ∈ s, (0 : ℝ) ≤ 1 / (i : ℝ) := fun _ _ _ => by positivity
  constructor
  · have := Finset.single_le_sum (f := fun v : ℕ => (1 : ℝ) / v) (hnn _)
      (two_mem_Vset (τ := τ) (y := y))
    simpa [HV] using this
  · -- `∑_{w ∈ W} 1/w ≤ |W|/y² ≤ 1`
    have hy : (0 : ℝ) < (y : ℝ) ^ 2 := by have := hL.y_ge; positivity
    have hWsum : ∑ w ∈ Wset y, (1 : ℝ) / w ≤ 1 := by
      have hcard : (Wset y).card ≤ y ^ 2 := by
        unfold Wset primesIn
        refine (Finset.card_filter_le _ _).trans ?_
        simp only [Nat.card_Ioc]
        omega
      calc ∑ w ∈ Wset y, (1 : ℝ) / w ≤ ∑ w ∈ Wset y, (1 : ℝ) / (y : ℝ) ^ 2 := by
            refine Finset.sum_le_sum (fun w hw => ?_)
            have h1 := (mem_Wset.1 hw).1
            have h2 : (y : ℝ) ^ 2 ≤ w := by exact_mod_cast h1.le
            exact one_div_le_one_div_of_le hy h2
        _ = (Wset y).card / (y : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ 1 := by
            rw [div_le_one hy]; exact_mod_cast hcard
    have hunion : ∑ v ∈ Bset τ ∪ Wset y, (1 : ℝ) / v ≤
        ∑ r ∈ Bset τ, (1 : ℝ) / r + ∑ w ∈ Wset y, (1 : ℝ) / w := by
      rw [← Finset.sum_union_inter]
      have := Finset.sum_nonneg (hnn (Bset τ ∩ Wset y))
      linarith
    have hins : HV τ y ≤ 1 / 2 + ∑ v ∈ Bset τ ∪ Wset y, (1 : ℝ) / v := by
      unfold HV Vset
      by_cases h2 : 2 ∈ Bset τ ∪ Wset y
      · rw [Finset.insert_eq_of_mem h2]; linarith
      · rw [Finset.sum_insert h2]; norm_num
    linarith

/-- `H_V > 0`. -/
lemma HV_pos (hL : Large τ y) : 0 < HV τ y := by
  have := (HV_bounds hL).1; linarith

end facts

/-! ### Lemma 4.1 (Tuning) -/

/-- Auxiliary: `U(y^8) = ∅`. -/
lemma Uset_eq_empty (y : ℕ) : Uset y (y ^ 8) = ∅ := by
  ext u; simp only [mem_Uset, Finset.notMem_empty, iff_false]; omega

/-- Adding the next integer `Y+1` adds at most one prime, of reciprocal `< 1/y^8`. -/
lemma sumU_succ_le {y Y : ℕ} (hy : 0 < y) (hY : y ^ 8 ≤ Y) :
    ∑ u ∈ Uset y (Y + 1), (1 : ℝ) / u ≤ ∑ u ∈ Uset y Y, (1 : ℝ) / u + 1 / (y : ℝ) ^ 8 := by
  have hsub : Uset y (Y + 1) ⊆ insert (Y + 1) (Uset y Y) := by
    intro u hu
    obtain ⟨h1, h2, h3⟩ := mem_Uset.1 hu
    rcases Nat.lt_or_ge u (Y + 1) with h | h
    · exact Finset.mem_insert_of_mem (mem_Uset.2 ⟨h1, by omega, h3⟩)
    · rw [show u = Y + 1 by omega]; exact Finset.mem_insert_self _ _
  have hnotin : Y + 1 ∉ Uset y Y := by intro h; have := (mem_Uset.1 h).2.1; omega
  calc ∑ u ∈ Uset y (Y + 1), (1 : ℝ) / u ≤ ∑ u ∈ insert (Y + 1) (Uset y Y), (1 : ℝ) / u :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = 1 / ((Y + 1 : ℕ) : ℝ) + ∑ u ∈ Uset y Y, (1 : ℝ) / u := Finset.sum_insert hnotin
    _ ≤ ∑ u ∈ Uset y Y, (1 : ℝ) / u + 1 / (y : ℝ) ^ 8 := by
        have : (y : ℝ) ^ 8 ≤ ((Y + 1 : ℕ) : ℝ) := by push_cast; exact_mod_cast (by omega : y ^ 8 ≤ Y + 1)
        have hpos : (0 : ℝ) < (y : ℝ) ^ 8 := by positivity
        have := one_div_le_one_div_of_le hpos this; linarith

/-- `∑_{u ∈ U} 1/u ≤ |U|/y^8`. -/
lemma sumU_le_card {y Y : ℕ} (hy : 0 < y) :
    ∑ u ∈ Uset y Y, (1 : ℝ) / u ≤ (Uset y Y).card / (y : ℝ) ^ 8 := by
  have hpos : (0 : ℝ) < (y : ℝ) ^ 8 := by positivity
  calc ∑ u ∈ Uset y Y, (1 : ℝ) / u ≤ ∑ u ∈ Uset y Y, 1 / (y : ℝ) ^ 8 := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        have h1 := (mem_Uset.1 hu).1
        exact one_div_le_one_div_of_le hpos (by exact_mod_cast h1.le)
    _ = (Uset y Y).card / (y : ℝ) ^ 8 := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Lemma 4.1 (Tuning).**  For `0 < τ ≤ η = 1/400` and `y` large, there is an endpoint
`Y ∈ [y^8, y^9]` with `0 ≤ τ - μ(Y) ≤ H_V/(2y^8)`, `μ(Y) ≥ τ/2` and `|U| ≥ τ y^8 / H_V`.
(Add the primes of `(y^8, y^9]` one at a time; stop at the last point where `μ ≤ τ`.) -/
theorem lem_tuning {τ : ℚ} {y : ℕ} (h0 : 0 < τ) (hη : τ ≤ 1 / 400) (hL : Large τ y) :
    ∃ Y, Tuned τ y Y := by
  classical
  have hτ0 : (0 : ℝ) < τ := by exact_mod_cast h0
  have hτη : (τ : ℝ) ≤ 1 / 400 := by
    have := (Rat.cast_le (K := ℝ)).2 hη; simpa using this
  have hHV := HV_bounds hL
  have hHVpos := HV_pos hL
  have hy : 0 < y := by have := hL.y_ge; omega
  have hy8 : y ^ 8 ≤ y ^ 9 := Nat.pow_le_pow_right hy (by norm_num)
  set T := (Finset.Icc (y ^ 8) (y ^ 9)).filter (fun Z => mu τ y Z ≤ τ) with hT
  have hne : y ^ 8 ∈ T := by
    simp only [hT, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨le_rfl, hy8⟩, ?_⟩
    rw [mu_eq, Uset_eq_empty]; simp; exact h0.le
  set Y := T.max' ⟨_, hne⟩ with hYdef
  have hYT : Y ∈ T := Finset.max'_mem _ _
  simp only [hT, Finset.mem_filter, Finset.mem_Icc] at hYT
  obtain ⟨⟨hYlo, hYhi⟩, hmuY⟩ := hYT
  -- the full range has `μ(y^9) ≥ c_U/4 = 1/200 > τ`
  have hfull : τ < mu τ y (y ^ 9) := by
    rw [mu_eq]
    have := hL.mertens
    have : (1 : ℝ) / 2 * (1 / 2) * (1 / 50) ≤ 1 / 2 * HV τ y * ∑ u ∈ Uset y (y ^ 9), (1 : ℝ) / u := by
      gcongr
      linarith [hHV.1]
    linarith
  have hYlt : Y < y ^ 9 := by
    rcases lt_or_eq_of_le hYhi with h | h
    · exact h
    · rw [h] at hmuY; linarith
  have hnext : τ < mu τ y (Y + 1) := by
    by_contra hcon
    push_neg at hcon
    have hmem : Y + 1 ∈ T := by
      simp only [hT, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hcon⟩
    have := Finset.le_max' T (Y + 1) hmem
    rw [← hYdef] at this
    omega
  have hstep : mu τ y (Y + 1) ≤ mu τ y Y + HV τ y / (2 * (y : ℝ) ^ 8) := by
    rw [mu_eq, mu_eq]
    have := sumU_succ_le (y := y) hy hYlo
    have h2 : 0 ≤ 1 / 2 * HV τ y := by positivity
    have := mul_le_mul_of_nonneg_left this h2
    have e : 1 / 2 * HV τ y * (1 / (y : ℝ) ^ 8) = HV τ y / (2 * (y : ℝ) ^ 8) := by
      field_simp
    nlinarith
  have hbeta : (τ : ℝ) - mu τ y Y ≤ HV τ y / (2 * (y : ℝ) ^ 8) := by linarith
  have hmu : (τ : ℝ) / 2 ≤ mu τ y Y := by linarith [hL.tune]
  refine ⟨Y, hYlo, hYhi, hmuY, hbeta, hmu, ?_⟩
  -- `∑_U 1/u = 2μ/H_V ≥ τ/H_V` and `∑_U 1/u ≤ |U|/y^8`
  have hsum : (τ : ℝ) / HV τ y ≤ ∑ u ∈ Uset y Y, (1 : ℝ) / u := by
    rw [div_le_iff₀ hHVpos]
    have := mu_eq (τ := τ) (y := y) (Y := Y)
    nlinarith
  have hcard := sumU_le_card (Y := Y) hy
  have hy8pos : (0 : ℝ) < (y : ℝ) ^ 8 := by positivity
  have := hsum.trans hcard
  rw [le_div_iff₀ hy8pos] at this
  calc (τ : ℝ) * (y : ℝ) ^ 8 / HV τ y = (τ : ℝ) / HV τ y * (y : ℝ) ^ 8 := by ring
    _ ≤ _ := this

/-! ### A congruence mod 1 forces equality (end of §4) -/

/-- The total mass of the graph is `2μ ≤ 2τ ≤ 1/2`, so every `S ⊆ A` has `0 ≤ σ(S) ≤ 1/2`. -/
lemma sigma_le_half {τ : ℚ} {y Y : ℕ} (hη : τ ≤ 1 / 400) (hT : Tuned τ y Y)
    {S : Finset (ℕ × ℕ)} (hS : S ⊆ Aset τ y Y) : 0 ≤ sigma S ∧ sigma S ≤ 1 / 2 := by
  have hnn : ∀ p : ℕ × ℕ, (0 : ℚ) ≤ 1 / ((p.1 : ℚ) * p.2) := fun _ => by positivity
  refine ⟨Finset.sum_nonneg (fun p _ => hnn p), ?_⟩
  have h1 : sigma S ≤ sigma (Aset τ y Y) :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun p _ _ => hnn p)
  have h2 : ((sigma (Aset τ y Y) : ℚ) : ℝ) = 2 * mu τ y Y := by
    unfold sigma mu; push_cast; ring
  have h3 : ((sigma (Aset τ y Y) : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by
    rw [h2]
    have := hT.beta_nonpos
    have : (τ : ℝ) ≤ 1 / 400 := by have := (Rat.cast_le (K := ℝ)).2 hη; simpa using this
    push_cast; linarith
  exact h1.trans (by exact_mod_cast h3)

/-- If `σ(S) ≡ τ (mod 1)` then `σ(S) = τ` (end of §4). -/
lemma sigma_eq_of_congr {τ : ℚ} {y Y : ℕ} (h0 : 0 < τ) (hη : τ ≤ 1 / 400) (hT : Tuned τ y Y)
    {S : Finset (ℕ × ℕ)} (hS : S ⊆ Aset τ y Y) (k : ℤ) (hk : sigma S - τ = k) :
    sigma S = τ := by
  obtain ⟨hs0, hs1⟩ := sigma_le_half hη hT hS
  have hk1 : (k : ℚ) < 1 := by rw [← hk]; linarith
  have hk2 : (-1 : ℚ) < k := by rw [← hk]; linarith
  have : k = 0 := by
    have a : k < 1 := by exact_mod_cast hk1
    have b : -1 < k := by exact_mod_cast hk2
    omega
  rw [this] at hk
  simp at hk
  linarith

end Erdos306
