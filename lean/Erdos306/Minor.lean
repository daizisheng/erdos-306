/-
§9 of the paper: Cases II and III, the minor arcs (Proposition 9.1).
-/
import Erdos306.Columns

namespace Erdos306

open Real Finset

attribute [local instance] Classical.propDecidable

variable {τ : ℚ} {y Y : ℕ}

/-! ### Generic helpers -/

/-- A single factor bounds a product of factors in `[0,1]`. -/
lemma prod_le_single_of_le_one {s : Finset ℕ} {f : ℕ → ℝ} {a : ℕ} (ha : a ∈ s)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ f a := by
  have := Finset.prod_le_prod_of_subset_of_le_one (Finset.singleton_subset_iff.2 ha) h0
    (fun i hi _ => h1 i hi)
  simpa using this

/-- `∏ (a_u + R_u) - ∏ a_u ≤ (1 + r)^n - 1` for `0 ≤ a_u ≤ 1`, `0 ≤ R_u ≤ r` (this is the
expansion over the set `T` of mismatched columns in the proof of Prop. 9.1, case II). -/
lemma prod_add_sub_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (a R : ι → ℝ) (r : ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) (hR0 : ∀ i ∈ s, 0 ≤ R i)
    (hR : ∀ i ∈ s, R i ≤ r) :
    ∏ i ∈ s, (a i + R i) - ∏ i ∈ s, a i ≤ (1 + r) ^ s.card - 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    have ha0' := fun i hi => ha0 i (Finset.mem_insert_of_mem hi)
    have ha1' := fun i hi => ha1 i (Finset.mem_insert_of_mem hi)
    have hR0' := fun i hi => hR0 i (Finset.mem_insert_of_mem hi)
    have hR' := fun i hi => hR i (Finset.mem_insert_of_mem hi)
    have ih' := ih ha0' ha1' hR0' hR'
    have hj0 := ha0 j (Finset.mem_insert_self j s)
    have hj1 := ha1 j (Finset.mem_insert_self j s)
    have hRj0 := hR0 j (Finset.mem_insert_self j s)
    have hRj := hR j (Finset.mem_insert_self j s)
    set P := ∏ i ∈ s, (a i + R i)
    set Q := ∏ i ∈ s, a i
    have hQ0 : 0 ≤ Q := Finset.prod_nonneg ha0'
    have hQP : Q ≤ P := Finset.prod_le_prod ha0' (fun i hi => by linarith [hR0' i hi])
    have hr0 : 0 ≤ r := hRj0.trans hRj
    have hP : P ≤ (1 + r) ^ s.card := by
      calc P ≤ ∏ i ∈ s, (1 + r) := Finset.prod_le_prod
            (fun i hi => by linarith [ha0' i hi, hR0' i hi])
            (fun i hi => by linarith [ha1' i hi, hR' i hi])
        _ = (1 + r) ^ s.card := Finset.prod_const _
    -- `(a+R)P - aQ = a(P - Q) + R P`
    have e : (a j + R j) * P - a j * Q = a j * (P - Q) + R j * P := by ring
    rw [e, pow_succ]
    have h1 : a j * (P - Q) ≤ (1 + r) ^ s.card - 1 := by
      calc a j * (P - Q) ≤ 1 * (P - Q) := mul_le_mul_of_nonneg_right hj1 (by linarith)
        _ ≤ _ := by linarith
    have h2 : R j * P ≤ r * (1 + r) ^ s.card :=
      mul_le_mul hRj hP (hQ0.trans hQP) hr0
    nlinarith

/-- `(1 + z)^n - 1 ≤ n z e^{n z}` for `z ≥ 0`. -/
lemma one_add_pow_sub_one_le (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    (1 + z) ^ n - 1 ≤ n * z * exp (n * z) := by
  have h1 : (1 + z) ^ n ≤ exp (n * z) := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by linarith)
    linarith [Real.add_one_le_exp z]
  have h2 : exp (n * z) - 1 ≤ n * z * exp (n * z) := by
    have := Real.add_one_le_exp (-(n * z))
    have hpos := Real.exp_pos (n * z)
    have e : exp (-(n * z)) * exp (n * z) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  linarith

/-- For `u ∈ U`, a column label is an element of `range u`. -/
lemma toNat_emod_lt {h : ℤ} {m : ℕ} (hm : 0 < m) : (h % (m : ℤ)).toNat < m := by
  have h1 : 0 ≤ h % (m : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hm.ne')
  have h2 : h % (m : ℤ) < m := Int.emod_lt_of_pos _ (by exact_mod_cast hm)
  omega

/-- `m ∣ h - (h mod m)`. -/
lemma dvd_sub_toNat_emod (h : ℤ) {m : ℕ} (hm : 0 < m) : (m : ℤ) ∣ h - ((h % (m : ℤ)).toNat : ℤ) := by
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))]
  exact Int.dvd_self_sub_emod

/-- Column bound: with at most one heavy label and every label of weight at most `c`,
`S_u(ξ) ≤ c + u ε`. -/
lemma Scol_le_of_heavy (hL : Large τ y) (hT : Tuned τ y Y) {u : ℕ} (hu : u ∈ Uset y Y) (ξ : ℕ)
    {c : ℝ} (hc : ∀ z, Fcol τ y u ξ z ≤ c) : Scol τ y u ξ ≤ c + u * eps y := by
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  have hc0 : 0 ≤ c := (Fcol_nonneg u ξ 0).trans (hc 0)
  unfold Scol
  by_cases hheavy : ∃ z0 ∈ range u, eps y < Fcol τ y u ξ z0
  · obtain ⟨z0, hz0, hz0h⟩ := hheavy
    rw [← Finset.add_sum_erase _ _ hz0]
    have hrest : ∑ z ∈ (range u).erase z0, Fcol τ y u ξ z ≤ ((range u).erase z0).card * eps y := by
      have : ∀ z ∈ (range u).erase z0, Fcol τ y u ξ z ≤ eps y := by
        intro z hz
        by_contra hcon
        push_neg at hcon
        have hdvd := heavy_unique hL hT.hi hu ξ z z0 hcon hz0h
        have hz := Finset.mem_erase.1 hz
        have h1 := Finset.mem_range.1 hz.2
        have h2 := Finset.mem_range.1 hz0
        have : (z : ℤ) - z0 = 0 := by
          apply Int.eq_zero_of_abs_lt_dvd hdvd
          rw [abs_lt]; constructor <;> omega
        omega
      calc _ ≤ ∑ z ∈ (range u).erase z0, eps y := Finset.sum_le_sum this
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (((range u).erase z0).card : ℝ) ≤ u := by
      rw [Finset.card_erase_of_mem hz0, Finset.card_range]
      exact_mod_cast Nat.sub_le u 1
    have := mul_le_mul_of_nonneg_right hcard heps0
    linarith [hc z0]
  · push_neg at hheavy
    calc ∑ z ∈ range u, Fcol τ y u ξ z ≤ ∑ z ∈ range u, eps y := Finset.sum_le_sum hheavy
      _ = u * eps y := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ c + u * eps y := by linarith

/-- Proposition 9.1, case III, one column: for incoherent `ξ`, `S_u(ξ) ≤ e^{-δ_a²}`.
(By Lemma 8.4 every label has an entry with phase `> δ_a`, so weight `≤ e^{-2δ_a²}`; by
Lemma 8.3(i) at most one label is heavy, the others have weight `≤ ε`.) -/
theorem caseIII_column (hL : Large τ y) (hT : Tuned τ y Y) {u : ℕ} (hu : u ∈ Uset y Y) (ξ : ℕ)
    (hξ : ¬ Coherent τ y ξ) : Scol τ y u ξ ≤ exp (-(deltaA y ^ 2)) := by
  -- every label has an entry with phase `> δ_a` (Lemma 8.4), so weight `≤ e^{-2δ_a²}`
  have hc : ∀ z, Fcol τ y u ξ z ≤ exp (-2 * deltaA y ^ 2) := by
    intro z
    have : ¬ ∀ v ∈ Vset τ y, nint (phase τ y u v ξ z) ≤ deltaA y :=
      fun h => hξ (coherent_of_admissible hL hT.hi hu ξ z h)
    push_neg at this
    obtain ⟨v, hv, hvd⟩ := this
    have hδa : 0 ≤ deltaA y := by rw [deltaA]; positivity
    calc Fcol τ y u ξ z ≤ |Real.cos (π * phase τ y u v ξ z)| :=
          prod_le_single_of_le_one hv (fun _ _ => abs_nonneg _) (fun _ _ => Real.abs_cos_le_one _)
      _ ≤ exp (-2 * nint (phase τ y u v ξ z) ^ 2) := lem_cos _
      _ ≤ exp (-2 * deltaA y ^ 2) := by
          apply Real.exp_le_exp.2
          nlinarith
  have h1 := Scol_le_of_heavy hL hT hu ξ hc
  have hu9 : (u : ℝ) ≤ (y : ℝ) ^ 9 := by
    exact_mod_cast (bounds_of_mem_Uset hu).2.trans hT.hi
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  have := mul_le_mul_of_nonneg_right hu9 heps0
  linarith [hL.colIII]

/-- Proposition 9.1, case III: `∑_{ξ incoherent} ∏_u S_u(ξ) ≤ 2b·16^{y²} e^{-δ_a²|U|} ≤ 1/4`. -/
theorem caseIII_total (hL : Large τ y) (hT : Tuned τ y Y) :
    ∑ ξ ∈ (range (PV τ y)).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)), ∏ u ∈ Uset y Y, Scol τ y u ξ
      ≤ 1 / 4 := by
  set X := exp (-(deltaA y ^ 2)) ^ (Uset y Y).card with hX
  have h1 : ∀ ξ ∈ (range (PV τ y)).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)),
      ∏ u ∈ Uset y Y, Scol τ y u ξ ≤ X := by
    intro ξ hξ
    have hξ' := (Finset.mem_filter.1 hξ).2
    calc ∏ u ∈ Uset y Y, Scol τ y u ξ ≤ ∏ u ∈ Uset y Y, exp (-(deltaA y ^ 2)) :=
          Finset.prod_le_prod (fun u _ => Scol_nonneg u ξ)
            (fun u hu => caseIII_column hL hT hu ξ hξ')
      _ = X := Finset.prod_const _
  have hX0 : 0 ≤ X := by positivity
  have h2 : ∑ ξ ∈ (range (PV τ y)).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)),
      ∏ u ∈ Uset y Y, Scol τ y u ξ ≤ (PV τ y : ℝ) * X := by
    calc _ ≤ ∑ ξ ∈ (range (PV τ y)).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)), X :=
          Finset.sum_le_sum h1
      _ = (((range (PV τ y)).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ))).card : ℝ) * X := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (PV τ y : ℝ) * X := by
          apply mul_le_mul_of_nonneg_right _ hX0
          have := Finset.card_filter_le (range (PV τ y)) (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ))
          rw [Finset.card_range] at this
          exact_mod_cast this
  -- `e^{-δ_a² |U|} ≤ exp(-τ y⁴/(64 H_V))` since `|U| ≥ τ y^8/H_V`
  have hHV := HV_pos hL
  have hy0 : (0 : ℝ) < y := by have := hL.y_ge; exact_mod_cast (by omega : 0 < y)
  have h3 : X ≤ exp (-((τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y))) := by
    rw [hX, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hU := hT.card_U
    have e1 : deltaA y ^ 2 = 1 / (64 * (y : ℝ) ^ 4) := by rw [deltaA]; field_simp; ring
    rw [e1]
    have e2 : (τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y) =
        ((τ : ℝ) * (y : ℝ) ^ 8 / HV τ y) * (1 / (64 * (y : ℝ) ^ 4)) := by
      field_simp
    rw [e2]
    have : 0 ≤ 1 / (64 * (y : ℝ) ^ 4) := by positivity
    nlinarith
  have h4 := prod_V_le (τ := τ) (y := y)
  have h5 := hL.caseIII
  have hPV : (PV τ y : ℝ) = ((∏ v ∈ Vset τ y, v : ℕ) : ℝ) := rfl
  calc _ ≤ (PV τ y : ℝ) * X := h2
    _ ≤ (2 * (τ.den : ℝ) * 16 ^ (y ^ 2)) * exp (-((τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y))) := by
        apply mul_le_mul (hPV ▸ h4) h3 hX0 (by positivity)
    _ ≤ 1 / 4 := h5

/-- Proposition 9.1, case II, for one coherent `ξ ≡ M`: the frequencies with some mismatched
column contribute `∏_u S_u(ξ) - ∏_u F_u(ξ, M mod u) ≤ |U| Y ε e^{|U| Y ε}`. -/
theorem caseII_single (hL : Large τ y) (hT : Tuned τ y Y) {M : ℤ} (hM : |M| ≤ (y : ℤ) ^ 7) :
    ∏ u ∈ Uset y Y, Scol τ y u (M % (PV τ y : ℤ)).toNat
        - ∏ u ∈ Uset y Y, Fcol τ y u (M % (PV τ y : ℤ)).toNat (M % (u : ℤ)).toNat
      ≤ (Uset y Y).card * Y * eps y * exp ((Uset y Y).card * Y * eps y) := by
  set ξ := (M % (PV τ y : ℤ)).toNat with hξ
  set m : ℕ → ℕ := fun u => (M % (u : ℤ)).toNat with hm
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  have hy3 := hL.y_ge
  have hyR : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hPV0 : 0 < PV τ y := by
    have := PV_gt_y8 hL; omega
  -- the matching label `M mod u` has small phases in the test rows, so every mismatched label
  -- has weight `≤ ε` (Lemma 8.3(ii))
  have hmis : ∀ u ∈ Uset y Y, ∀ z ∈ (range u).erase (m u), Fcol τ y u ξ z ≤ eps y := by
    intro u hu z hz
    have hu0 : 0 < u := (prime_of_mem_Uset hu).pos
    have hz' := Finset.mem_erase.1 hz
    apply (lem_unique hL hT.hi hu ξ z (m u) ?_).2 ?_
    · intro hd
      have h1 := Finset.mem_range.1 hz'.2
      have h2 : m u < u := toNat_emod_lt hu0
      have : (z : ℤ) - (m u : ℕ) = 0 := by
        apply Int.eq_zero_of_abs_lt_dvd hd
        rw [abs_lt]; constructor <;> omega
      exact hz'.1 (by omega)
    · intro w hw
      have hwV := Wset_subset_Vset (τ := τ) hw
      have hwP : (w : ℤ) ∣ (PV τ y : ℤ) := by
        exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hwV
      obtain ⟨n, hn⟩ := phase_congr hL hu hwV ξ (m u) M
        (hwP.trans (dvd_sub_toNat_emod M hPV0)) (dvd_sub_toNat_emod M hu0)
      rw [hn, nint_add_int]
      obtain ⟨hw1, -, -⟩ := mem_Wset.1 hw
      obtain ⟨hu1, -, -⟩ := mem_Uset.1 hu
      have hw1' : (y : ℝ) ^ 2 < w := by exact_mod_cast hw1
      have hu1' : (y : ℝ) ^ 8 < u := by exact_mod_cast hu1
      have hM' : |(M : ℝ)| ≤ (y : ℝ) ^ 7 := by
        have : ((|M| : ℤ) : ℝ) ≤ (((y : ℤ) ^ 7 : ℤ) : ℝ) := by exact_mod_cast hM
        push_cast at this; exact this
      have huw : (y : ℝ) ^ 10 < (u : ℝ) * w := by
        have : (y : ℝ) ^ 10 = (y : ℝ) ^ 8 * (y : ℝ) ^ 2 := by ring
        rw [this]
        exact mul_lt_mul'' hu1' hw1' (by positivity) (by positivity)
      calc nint ((M : ℝ) / ((u : ℝ) * w)) ≤ |(M : ℝ) / ((u : ℝ) * w)| := nint_le_abs _
        _ = |(M : ℝ)| / ((u : ℝ) * w) := by
            rw [abs_div, abs_of_pos (a := (u : ℝ) * w) (lt_trans (by positivity) huw)]
        _ ≤ (y : ℝ) ^ 7 / (y : ℝ) ^ 10 := by
            exact div_le_div₀ (by positivity) hM' (by positivity) huw.le
        _ = 1 / (y : ℝ) ^ 3 := by field_simp
        _ ≤ delta y / 2 := hL.phase
  -- `S_u = F_u(ξ, M mod u) + R_u` with `R_u ≤ Y ε`
  set R : ℕ → ℝ := fun u => ∑ z ∈ (range u).erase (m u), Fcol τ y u ξ z with hR
  have hS : ∀ u ∈ Uset y Y, Scol τ y u ξ = Fcol τ y u ξ (m u) + R u := by
    intro u hu
    unfold Scol
    rw [hR, Finset.add_sum_erase _ _ (Finset.mem_range.2 (toNat_emod_lt (prime_of_mem_Uset hu).pos))]
  have hRb : ∀ u ∈ Uset y Y, R u ≤ Y * eps y := by
    intro u hu
    calc R u ≤ ∑ z ∈ (range u).erase (m u), eps y := Finset.sum_le_sum (hmis u hu)
      _ = (((range u).erase (m u)).card : ℝ) * eps y := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Y * eps y := by
          apply mul_le_mul_of_nonneg_right _ heps0
          have h1 := Finset.card_erase_le (s := range u) (a := m u)
          rw [Finset.card_range] at h1
          have h2 := (bounds_of_mem_Uset hu).2
          exact_mod_cast h1.trans h2
  have hR0 : ∀ u ∈ Uset y Y, 0 ≤ R u := fun u _ => Finset.sum_nonneg (fun _ _ => Fcol_nonneg _ _ _)
  rw [Finset.prod_congr rfl hS]
  have := prod_add_sub_prod_le (Uset y Y) (fun u => Fcol τ y u ξ (m u)) R (Y * eps y)
    (fun u _ => Fcol_nonneg _ _ _) (fun u _ => Fcol_le_one _ _ _) hR0 hRb
  refine this.trans ?_
  have h := one_add_pow_sub_one_le (Uset y Y).card (z := Y * eps y) (by positivity)
  calc _ ≤ _ := h
    _ = _ := by ring_nf


/-- Proposition 9.1, case II: summing over the `2y^7+1 ≤ 3y^7` values of `M` gives `≤ 1/4`. -/
theorem caseII_total (hL : Large τ y) (hT : Tuned τ y Y) :
    ∑ M ∈ Finset.Icc (-(y : ℤ) ^ 7) ((y : ℤ) ^ 7),
      (∏ u ∈ Uset y Y, Scol τ y u (M % (PV τ y : ℤ)).toNat
        - ∏ u ∈ Uset y Y, Fcol τ y u (M % (PV τ y : ℤ)).toNat (M % (u : ℤ)).toNat) ≤ 1 / 4 := by
  set B := ((Uset y Y).card : ℝ) * Y * eps y * exp ((Uset y Y).card * Y * eps y) with hB
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  have hy3 := hL.y_ge
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast (by omega : 1 ≤ y)
  have hYR : (Y : ℝ) ≤ (y : ℝ) ^ 9 := by exact_mod_cast hT.hi
  have hUR : ((Uset y Y).card : ℝ) ≤ (y : ℝ) ^ 9 := by
    have : (Uset y Y).card ≤ Y := by
      calc (Uset y Y).card ≤ (Finset.Ioc (y ^ 8) Y).card := Finset.card_filter_le _ _
        _ = Y - y ^ 8 := Nat.card_Ioc _ _
        _ ≤ Y := Nat.sub_le _ _
    exact le_trans (by exact_mod_cast this) hYR
  have hUY : ((Uset y Y).card : ℝ) * Y * eps y ≤ (y : ℝ) ^ 18 * eps y := by
    have : ((Uset y Y).card : ℝ) * Y ≤ (y : ℝ) ^ 9 * (y : ℝ) ^ 9 :=
      mul_le_mul hUR hYR (by positivity) (by positivity)
    have e : (y : ℝ) ^ 18 = (y : ℝ) ^ 9 * (y : ℝ) ^ 9 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right this heps0
  have hB' : B ≤ (y : ℝ) ^ 18 * eps y * exp ((y : ℝ) ^ 18 * eps y) := by
    rw [hB]
    apply mul_le_mul hUY (Real.exp_le_exp.2 hUY) (by positivity) (by positivity)
  have hcard : ((Finset.Icc (-(y : ℤ) ^ 7) ((y : ℤ) ^ 7)).card : ℝ) ≤ 3 * (y : ℝ) ^ 7 := by
    rw [Int.card_Icc]
    have h7 : (1 : ℤ) ≤ (y : ℤ) ^ 7 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ y))
    have : ((y : ℤ) ^ 7 + 1 - -(y : ℤ) ^ 7).toNat ≤ 3 * y ^ 7 := by
      have : ((y : ℤ) ^ 7 + 1 - -(y : ℤ) ^ 7) ≤ 3 * (y : ℤ) ^ 7 := by linarith
      have h' : (((3 * y ^ 7 : ℕ)) : ℤ) = 3 * (y : ℤ) ^ 7 := by push_cast; ring
      omega
    exact_mod_cast this
  calc _ ≤ ∑ M ∈ Finset.Icc (-(y : ℤ) ^ 7) ((y : ℤ) ^ 7), B := by
        apply Finset.sum_le_sum
        intro M hM
        have hM' : |M| ≤ (y : ℤ) ^ 7 := abs_le.2 (Finset.mem_Icc.1 hM)
        exact caseII_single hL hT hM'
    _ = ((Finset.Icc (-(y : ℤ) ^ 7) ((y : ℤ) ^ 7)).card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * (y : ℝ) ^ 7) * ((y : ℝ) ^ 18 * eps y * exp ((y : ℝ) ^ 18 * eps y)) :=
        mul_le_mul hcard hB' (by positivity) (by positivity)
    _ = 3 * (y : ℝ) ^ 25 * eps y * exp ((y : ℝ) ^ 18 * eps y) := by ring
    _ ≤ 1 / 4 := hL.caseII


/-- Passing from frequencies to labels (via eq. (4) and the injectivity of the label map):
the case III frequencies contribute at most `∑_{ξ incoherent} ∏_u S_u(ξ)`, and the case II
frequencies at most `∑_M (∏_u S_u(M) - ∏_u F_u(M, M mod u))`. -/
theorem minor_le_labels (hL : Large τ y) :
    ∑ h ∈ (freq (Lnum τ y Y)).filter (fun h => CaseII τ y Y h ∨ CaseIII τ y h),
        ‖phi (Aset τ y Y) h‖
      ≤ ∑ ξ ∈ (range (PV τ y)).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)), ∏ u ∈ Uset y Y, Scol τ y u ξ
        + ∑ M ∈ Finset.Icc (-(y : ℤ) ^ 7) ((y : ℤ) ^ 7),
          (∏ u ∈ Uset y Y, Scol τ y u (M % (PV τ y : ℤ)).toNat
            - ∏ u ∈ Uset y Y, Fcol τ y u (M % (PV τ y : ℤ)).toNat (M % (u : ℤ)).toNat) := by
  set L := Lnum τ y Y with hLdef
  set P := PV τ y with hPdef
  have hP0 : 0 < P := by have := PV_gt_y8 hL; omega
  have hP0' : (P : ℤ) ≠ 0 := by exact_mod_cast hP0.ne'
  -- the label map `h ↦ (ξ, ζ)` and the column-product `G(ξ, ζ) = ∏_u F_u(ξ, ζ_u)`
  let col : ℤ → (Uset y Y → ℕ) := fun h u => (h % ((u : ℕ) : ℤ)).toNat
  let lab : ℤ → ℕ × (Uset y Y → ℕ) := fun h => ((h % (P : ℤ)).toNat, col h)
  let G : ℕ × (Uset y Y → ℕ) → ℝ := fun x => ∏ u : Uset y Y, Fcol τ y u x.1 (x.2 u)
  have hG0 : ∀ x, 0 ≤ G x := fun x => Finset.prod_nonneg (fun _ _ => Fcol_nonneg _ _ _)
  have hphi : ∀ h, ‖phi (Aset τ y Y) h‖ = G (lab h) := by
    intro h
    rw [norm_phi_eq_prod_Fcol hL]
    exact (Finset.prod_coe_sort (Uset y Y)
      (fun u => Fcol τ y u (h % (P : ℤ)).toNat (h % (u : ℤ)).toNat)).symm
  have hu0 : ∀ u : Uset y Y, 0 < (u : ℕ) := fun u => (prime_of_mem_Uset u.2).pos
  have hcol_mem : ∀ h, col h ∈ Fintype.piFinset (fun u : Uset y Y => range (u : ℕ)) := by
    intro h
    rw [Fintype.mem_piFinset]
    intro u
    exact Finset.mem_range.2 (toNat_emod_lt (hu0 u))
  -- equal column labels give divisibility by each `u`
  have hcol_dvd : ∀ h h', col h = col h' → ∀ u ∈ Uset y Y, (u : ℤ) ∣ h - h' := by
    intro h h' he u hu
    have := congrFun he ⟨u, hu⟩
    simp only [col] at this
    have h1 := Int.toNat_of_nonneg (Int.emod_nonneg h (b := (u : ℤ))
      (by exact_mod_cast (prime_of_mem_Uset hu).ne_zero))
    have h2 := Int.toNat_of_nonneg (Int.emod_nonneg h' (b := (u : ℤ))
      (by exact_mod_cast (prime_of_mem_Uset hu).ne_zero))
    have h3 : h % (u : ℤ) = h' % (u : ℤ) := by rw [← h1, ← h2, this]
    exact Int.ModEq.dvd h3.symm
  -- equal row labels give divisibility by `P_V`
  have hrow_dvd : ∀ h h', (h % (P : ℤ)).toNat = (h' % (P : ℤ)).toNat → (P : ℤ) ∣ h - h' := by
    intro h h' he
    have h1 := Int.toNat_of_nonneg (Int.emod_nonneg h hP0')
    have h2 := Int.toNat_of_nonneg (Int.emod_nonneg h' hP0')
    have h3 : h % (P : ℤ) = h' % (P : ℤ) := by rw [← h1, ← h2, he]
    exact Int.ModEq.dvd h3.symm
  -- Step 0: split cases II and III
  have hsplit : ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h ∨ CaseIII τ y h),
        ‖phi (Aset τ y Y) h‖ ≤
      ∑ h ∈ (freq L).filter (fun h => CaseIII τ y h), ‖phi (Aset τ y Y) h‖ +
      ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h), ‖phi (Aset τ y Y) h‖ := by
    rw [Finset.filter_or]
    have e := Finset.sum_union_inter (s₁ := (freq L).filter (fun h => CaseII τ y Y h))
      (s₂ := (freq L).filter (fun h => CaseIII τ y h)) (f := fun h => ‖phi (Aset τ y Y) h‖)
    have : 0 ≤ ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h) ∩
        (freq L).filter (fun h => CaseIII τ y h), ‖phi (Aset τ y Y) h‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  -- Step 1: case III, via the injective label map and eq. (4)
  have h3 : ∑ h ∈ (freq L).filter (fun h => CaseIII τ y h), ‖phi (Aset τ y Y) h‖ ≤
      ∑ ξ ∈ (range P).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)),
        ∏ u ∈ Uset y Y, Scol τ y u ξ := by
    set s := (freq L).filter (fun h => CaseIII τ y h)
    have hinj : Set.InjOn lab s := by
      intro h hh h' hh' he
      have hh := (Finset.mem_filter.1 hh).1
      have hh' := (Finset.mem_filter.1 hh').1
      have e1 := congrArg Prod.fst he
      have e2 := congrArg Prod.snd he
      exact label_inj hh hh' (hrow_dvd h h' e1) (hcol_dvd h h' e2)
    set T := (range P).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)) ×ˢ
      Fintype.piFinset (fun u : Uset y Y => range (u : ℕ))
    have himg : s.image lab ⊆ T := by
      intro x hx
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hx
      have hIII := (Finset.mem_filter.1 hh).2
      refine Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 (toNat_emod_lt hP0), ?_⟩,
        hcol_mem h⟩
      -- `h ≡ ξ (mod P_V)`, so coherence of `ξ` would give coherence of `h`
      rintro ⟨M, hM, hMv⟩
      apply hIII
      refine ⟨M, hM, fun v hv => ?_⟩
      have hvP : (v : ℤ) ∣ (P : ℤ) := by
        exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hv
      have := dvd_add (hvP.trans (dvd_sub_toNat_emod h hP0)) (hMv v hv)
      simp only [lab] at this
      have e : h - (((h % (P : ℤ)).toNat : ℕ) : ℤ) + ((((h % (P : ℤ)).toNat : ℕ) : ℤ) - M) =
        h - M := by ring
      rwa [e] at this
    calc ∑ h ∈ s, ‖phi (Aset τ y Y) h‖ = ∑ h ∈ s, G (lab h) := Finset.sum_congr rfl (fun h _ => hphi h)
      _ = ∑ x ∈ s.image lab, G x := (Finset.sum_image hinj).symm
      _ ≤ ∑ x ∈ T, G x := Finset.sum_le_sum_of_subset_of_nonneg himg (fun x _ _ => hG0 x)
      _ = _ := by
          rw [Finset.sum_product]
          refine Finset.sum_congr rfl (fun ξ _ => ?_)
          exact eq_factor ξ
  -- Step 2: case II.  First a union bound over the (unique) `M`.
  set K := (y : ℤ) ^ 7
  let Q : ℤ → ℤ → Prop := fun M h =>
    (∀ v ∈ Vset τ y, (v : ℤ) ∣ h - M) ∧ ∃ u ∈ Uset y Y, ¬ (u : ℤ) ∣ h - M
  have h2a : ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h), ‖phi (Aset τ y Y) h‖ ≤
      ∑ M ∈ Finset.Icc (-K) K, ∑ h ∈ (freq L).filter (Q M), ‖phi (Aset τ y Y) h‖ := by
    calc _ ≤ ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h),
          ∑ M ∈ Finset.Icc (-K) K, (if Q M h then ‖phi (Aset τ y Y) h‖ else 0) := by
          apply Finset.sum_le_sum
          intro h hh
          obtain ⟨M, hM, hMv, hMu⟩ := (Finset.mem_filter.1 hh).2
          have hMI : M ∈ Finset.Icc (-K) K := Finset.mem_Icc.2 (abs_le.1 hM)
          have := Finset.single_le_sum (f := fun M => if Q M h then ‖phi (Aset τ y Y) h‖ else 0)
            (fun M _ => by positivity) hMI
          simp only at this
          rw [if_pos ⟨hMv, hMu⟩] at this
          exact this
      _ = ∑ M ∈ Finset.Icc (-K) K, ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h),
          (if Q M h then ‖phi (Aset τ y Y) h‖ else 0) := Finset.sum_comm
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro M _
          rw [← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro h hh
            simp only [Finset.mem_filter] at hh ⊢
            exact ⟨hh.1.1, hh.2⟩
          · intros; exact norm_nonneg _
  -- For fixed `M`: inject `h ↦ ζ(h)` into the mismatched column labels.
  have h2b : ∀ M ∈ Finset.Icc (-K) K, ∑ h ∈ (freq L).filter (Q M), ‖phi (Aset τ y Y) h‖ ≤
      ∏ u ∈ Uset y Y, Scol τ y u (M % (P : ℤ)).toNat
        - ∏ u ∈ Uset y Y, Fcol τ y u (M % (P : ℤ)).toNat (M % (u : ℤ)).toNat := by
    intro M _
    set ξM := (M % (P : ℤ)).toNat
    set s := (freq L).filter (Q M)
    let G' : (Uset y Y → ℕ) → ℝ := fun ζ => ∏ u : Uset y Y, Fcol τ y u ξM (ζ u)
    have hPdvd : ∀ h ∈ s, (P : ℤ) ∣ h - M := by
      intro h hh
      exact prod_primes_dvd_int _ (fun v hv => prime_of_mem_Vset hv) _
        (Finset.mem_filter.1 hh).2.1
    have hrow : ∀ h ∈ s, (h % (P : ℤ)).toNat = ξM := by
      intro h hh
      have : h % (P : ℤ) = M % (P : ℤ) := (Int.modEq_iff_dvd.2 (hPdvd h hh)).symm
      simp only [ξM, this]
    have hinj : Set.InjOn col s := by
      intro h hh h' hh' he
      have hd : (P : ℤ) ∣ h - h' := by
        have := dvd_sub (hPdvd h hh) (hPdvd h' hh')
        have e : h - M - (h' - M) = h - h' := by ring
        rwa [e] at this
      exact label_inj (Finset.mem_filter.1 hh).1 (Finset.mem_filter.1 hh').1 hd
        (hcol_dvd h h' he)
    set ζM : Uset y Y → ℕ := col M
    have hζM : ζM ∈ Fintype.piFinset (fun u : Uset y Y => range (u : ℕ)) := hcol_mem M
    have himg : s.image col ⊆ (Fintype.piFinset (fun u : Uset y Y => range (u : ℕ))).erase ζM := by
      intro ζ hζ
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hζ
      refine Finset.mem_erase.2 ⟨fun he => ?_, hcol_mem h⟩
      obtain ⟨u, hu, hnd⟩ := (Finset.mem_filter.1 hh).2.2
      exact hnd (hcol_dvd h M he u hu)
    calc ∑ h ∈ s, ‖phi (Aset τ y Y) h‖ = ∑ h ∈ s, G' (col h) := by
          refine Finset.sum_congr rfl (fun h hh => ?_)
          rw [hphi h]
          simp only [G, G', lab, hrow h hh]
      _ = ∑ ζ ∈ s.image col, G' ζ := (Finset.sum_image hinj).symm
      _ ≤ ∑ ζ ∈ (Fintype.piFinset (fun u : Uset y Y => range (u : ℕ))).erase ζM, G' ζ :=
          Finset.sum_le_sum_of_subset_of_nonneg himg
            (fun ζ _ _ => Finset.prod_nonneg (fun _ _ => Fcol_nonneg _ _ _))
      _ = ∑ ζ ∈ Fintype.piFinset (fun u : Uset y Y => range (u : ℕ)), G' ζ - G' ζM :=
          Finset.sum_erase_eq_sub hζM
      _ = _ := by
          rw [eq_factor ξM]
          congr 1
          exact Finset.prod_coe_sort (Uset y Y)
            (fun u => Fcol τ y u ξM (M % (u : ℤ)).toNat)
  have h2 := h2a.trans (Finset.sum_le_sum h2b)
  linarith

/-- **Proposition 9.1 (minor arcs).**  For `y` large, `∑_{h in cases II and III} |φ(h)| ≤ 1/2`. -/
theorem prop_minor (hL : Large τ y) (hT : Tuned τ y Y) :
    ∑ h ∈ (freq (Lnum τ y Y)).filter (fun h => CaseII τ y Y h ∨ CaseIII τ y h),
        ‖phi (Aset τ y Y) h‖ ≤ 1 / 2 := by
  have h1 := minor_le_labels (Y := Y) hL
  have h2 := caseIII_total hL hT
  have h3 := caseII_total hL hT
  linarith

end Erdos306
