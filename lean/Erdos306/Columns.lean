/-
§8 of the paper: two lemmas about a single column.

* Lemma 8.1 (`lem_cos`):        `|cos πx| ≤ exp(-2‖x‖²)`;
* eq. (5) (`eq_pf`):              changing only the column label by `s` shifts the phase in row `v`
                                by `s v̄ / u (mod 1)`;
* Lemma 8.2 (`lem_count`):      few test primes are "invisible" (divisor count);
* Lemma 8.3 (`lem_unique`):     separation;
* Lemma 8.4 (`lem_admissible`): no wrap-around.

Inverses modulo `u` are avoided: "`‖s w̄/u‖ ≤ δ`" is expressed as
"`t w ≡ s (mod u)` for some integer `|t| ≤ δ u`" (`Invisible`); the two are equivalent, since
`t` is then the balanced representative of `s w̄` (see the proof of Lemma 8.2 in the paper).
-/
import Erdos306.Table

namespace Erdos306

open Real Finset

attribute [local instance] Classical.propDecidable

/-- **Lemma 8.1.**  For all real `x`, `|cos πx| ≤ exp(-2‖x‖²)`. -/
theorem lem_cos (x : ℝ) : |Real.cos (π * x)| ≤ exp (-2 * nint x ^ 2) := by
  set t := x - round x with ht
  -- `|cos πx|` has period 1 and is even, so `|cos πx| = cos πa` with `a = ‖x‖ ∈ [0, 1/2]`
  have hper : |Real.cos (π * x)| = |Real.cos (π * t)| := by
    have : π * x = π * t + ((round x : ℤ) : ℝ) * π := by rw [ht]; ring
    rw [this, Real.cos_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
  set a := nint x with ha
  have hat : a = |t| := rfl
  have ha0 : 0 ≤ a := nint_nonneg x
  have ha1 : a ≤ 1 / 2 := nint_le_half x
  have hcos_abs : |Real.cos (π * t)| = Real.cos (π * a) := by
    have h1 : Real.cos (π * t) = Real.cos (π * a) := by
      rw [hat]
      rcases abs_cases t with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]
      · rw [h, mul_neg, Real.cos_neg]
    rw [h1]
    apply abs_of_nonneg
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_pos]
  rw [hper, hcos_abs]
  have hc0 : 0 ≤ Real.cos (π * a) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_pos]
  -- `sin πa ≥ 2a` (concavity, i.e. Jordan's inequality)
  have hsin : 2 * a ≤ Real.sin (π * a) := by
    have := Real.mul_le_sin (x := π * a) (by positivity) (by nlinarith [Real.pi_pos])
    have e : 2 / π * (π * a) = 2 * a := by field_simp
    linarith
  -- `cos² πa = 1 - sin² πa ≤ 1 - 4a² ≤ e^{-4a²}`
  have hsq : Real.cos (π * a) ^ 2 ≤ exp (-4 * a ^ 2) := by
    have h1 : Real.cos (π * a) ^ 2 = 1 - Real.sin (π * a) ^ 2 := by
      rw [← Real.sin_sq_add_cos_sq (π * a)]; ring
    have h2 : (2 * a) ^ 2 ≤ Real.sin (π * a) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) hsin
    have h3 := Real.add_one_le_exp (-4 * a ^ 2)
    nlinarith
  by_contra hcon
  push_neg at hcon
  have : exp (-2 * a ^ 2) ^ 2 < Real.cos (π * a) ^ 2 :=
    pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
  rw [← Real.exp_nat_mul] at this
  have e : ((2 : ℕ) : ℝ) * (-2 * a ^ 2) = -4 * a ^ 2 := by push_cast; ring
  rw [e] at this
  linarith

variable {τ : ℚ} {y Y : ℕ}

/-- **eq. (5)**: two frequencies with the same row labels `ξ` and column labels `z, z'` at `u`:
their phases in row `v` differ by `k/u` where `v k ≡ z - z' (mod u)`, i.e. by `s v̄/u` with
`s = z - z'`. -/
lemma eq_pf (hL : Large τ y) {u v : ℕ} (hu : u ∈ Uset y Y) (hv : v ∈ Vset τ y) (ξ z z' : ℕ) :
    ∃ k : ℤ, (u : ℤ) ∣ (v : ℤ) * k - ((z : ℤ) - z') ∧
      phase τ y u v ξ z - phase τ y u v ξ z' = (k : ℝ) / u := by
  have hJ := crt_modEq_xi hL hu ξ z
  have hJ' := crt_modEq_xi hL hu ξ z'
  have hvP : (v : ℤ) ∣ (PV τ y : ℤ) := by
    exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hv
  -- `J ≡ J' (mod v)`, so `J - J' = v k`
  have hdv : (v : ℤ) ∣ ((crt τ y u ξ z : ℕ) : ℤ) - (crt τ y u ξ z' : ℕ) :=
    hvP.trans ((hJ.trans hJ'.symm).symm.dvd)
  obtain ⟨k, hk⟩ := hdv
  refine ⟨k, ?_, ?_⟩
  · have h1 := (crt_modEq_z hL hu ξ z).symm.dvd
    have h2 := (crt_modEq_z hL hu ξ z').symm.dvd
    rw [← hk]
    have := dvd_sub h1 h2
    have e : ((crt τ y u ξ z : ℕ) : ℤ) - (crt τ y u ξ z' : ℕ) - ((z : ℤ) - z') =
        ((crt τ y u ξ z : ℕ) - (z : ℤ)) - ((crt τ y u ξ z' : ℕ) - (z' : ℤ)) := by ring
    rw [e]; exact this
  · have hu0 : (0 : ℝ) < u := by exact_mod_cast (prime_of_mem_Uset hu).pos
    have hv0 : (0 : ℝ) < v := by exact_mod_cast (prime_of_mem_Vset hv).pos
    have hkR : ((crt τ y u ξ z : ℕ) : ℝ) - (crt τ y u ξ z' : ℕ) = (v : ℝ) * k := by
      have := congrArg (fun n : ℤ => (n : ℝ)) hk
      push_cast at this
      exact this
    unfold phase
    rw [div_sub_div_same, hkR]
    field_simp

/-- A test prime `w` is *invisible* for the shift `s` at the column `u` if `‖s w̄/u‖ ≤ δ`,
i.e. if `t w ≡ s (mod u)` for some integer `t` with `|t| ≤ δ u`. -/
def Invisible (d : ℝ) (u : ℕ) (s : ℤ) (w : ℕ) : Prop :=
  ∃ t : ℤ, |(t : ℝ)| ≤ d * u ∧ (u : ℤ) ∣ t * w - s

/-- **Lemma 8.2 (divisor count).**  Let `u ∈ U` and `s ≢ 0 (mod u)`.  If `y` is large, then
`#{w ∈ W : ‖s w̄/u‖ ≤ δ} ≤ 5(4δy² + 2) ≤ |W|/2`.
(Each invisible `w` divides one of the at most `4δy²+2` nonzero integers `s + uℓ`, of absolute
value at most `y^{11}`, and such an integer has at most `5` prime factors exceeding `y²`.) -/
theorem lem_count (hL : Large τ y) (hY : Y ≤ y ^ 9) {u : ℕ} (hu : u ∈ Uset y Y) {s : ℤ}
    (hs : ¬ (u : ℤ) ∣ s) :
    (((Wset y).filter (fun w => Invisible (delta y) u s w)).card : ℝ)
        ≤ 5 * (4 * delta y * (y : ℝ) ^ 2 + 2) ∧
      5 * (4 * delta y * (y : ℝ) ^ 2 + 2) ≤ ((Wset y).card : ℝ) / 2 := by
  have hy3 : 3 ≤ y := hL.y_ge
  have hyR : (3 : ℝ) ≤ y := by exact_mod_cast hy3
  have hlog : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) (by linarith)
  have hlog2 := Real.log_two_gt_d9
  have hlogpos : 0 < Real.log y := by linarith
  set δ := delta y with hδdef
  have hδ0 : 0 < δ := by rw [hδdef, delta]; positivity
  have hδ1 : 2 * δ ≤ 1 := by
    rw [hδdef, delta]
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  obtain ⟨hu8, huY, hup⟩ := mem_Uset.1 hu
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hup.pos
  have hu0' : (0 : ℤ) < u := by exact_mod_cast hup.pos
  have huy9 : (u : ℝ) ≤ (y : ℝ) ^ 9 := by exact_mod_cast huY.trans hY
  -- Step 0: take `s` balanced, `|s'| ≤ u/2`, `s' ≡ s (mod u)`.
  set s' : ℤ := s - u * round ((s : ℝ) / u) with hs'def
  have hs' : |(s' : ℝ)| ≤ u / 2 := by
    have h1 := abs_sub_round ((s : ℝ) / u)
    have e : (s' : ℝ) = u * ((s : ℝ) / u - round ((s : ℝ) / u)) := by
      rw [hs'def]; push_cast; field_simp
    rw [e, abs_mul, abs_of_pos hu0]
    nlinarith
  have hss' : (u : ℤ) ∣ s - s' := ⟨round ((s : ℝ) / u), by rw [hs'def]; ring⟩
  have hs'nd : ¬ (u : ℤ) ∣ s' := by
    intro h; exact hs (by have := dvd_add h hss'; simpa using this)
  -- Step 1: for each invisible `w` choose `t` with `|t| ≤ δu`, `t w ≡ s (mod u)`,
  -- and write `t w = s' + u ℓ`.
  set I := (Wset y).filter (fun w => Invisible δ u s w) with hIdef
  let tw : ℕ → ℤ := fun w => if h : Invisible δ u s w then Classical.choose h else 0
  have htw : ∀ w ∈ I, |((tw w : ℤ) : ℝ)| ≤ δ * u ∧ (u : ℤ) ∣ tw w * w - s := by
    intro w hw
    have hinv := (Finset.mem_filter.1 hw).2
    simp only [tw, dif_pos hinv]
    exact Classical.choose_spec hinv
  let ℓ : ℕ → ℤ := fun w => (tw w * w - s') / u
  have hℓeq : ∀ w ∈ I, tw w * w = s' + u * ℓ w := by
    intro w hw
    have h1 : (u : ℤ) ∣ tw w * w - s' := by
      have := dvd_add (htw w hw).2 hss'
      have e : tw w * ↑w - s + (s - s') = tw w * w - s' := by ring
      rwa [e] at this
    simp only [ℓ]
    rw [Int.mul_ediv_cancel' h1]; ring
  have hWb : ∀ w ∈ I, y ^ 2 < w ∧ w ≤ 2 * y ^ 2 ∧ w.Prime := fun w hw =>
    mem_Wset.1 (Finset.mem_filter.1 hw).1
  -- `|t w| ≤ δ u · 2y² ≤ u y² ≤ y^{11}`
  have htwb : ∀ w ∈ I, |((tw w * w : ℤ) : ℝ)| ≤ δ * u * (2 * (y : ℝ) ^ 2) := by
    intro w hw
    have h1 := (htw w hw).1
    have h2 : (w : ℝ) ≤ 2 * (y : ℝ) ^ 2 := by exact_mod_cast (hWb w hw).2.1
    push_cast
    rw [abs_mul, Nat.abs_cast]
    apply mul_le_mul h1 h2 (by positivity) (by positivity)
  -- Step 2: `|ℓ| ≤ 2δy² + 1/2`, so `ℓ` takes at most `4δy² + 2` values.
  set m : ℕ := ⌊2 * δ * (y : ℝ) ^ 2 + 1 / 2⌋₊ with hmdef
  have hℓm : ∀ w ∈ I, ℓ w ∈ Finset.Icc (-(m : ℤ)) m := by
    intro w hw
    have e := hℓeq w hw
    have h1 : (u : ℝ) * |((ℓ w : ℤ) : ℝ)| ≤ u * (2 * δ * (y : ℝ) ^ 2 + 1 / 2) := by
      have e' : ((u : ℤ) : ℝ) * ((ℓ w : ℤ) : ℝ) = ((tw w * w : ℤ) : ℝ) - (s' : ℝ) := by
        have := congrArg (fun n : ℤ => (n : ℝ)) e
        push_cast at this ⊢
        linarith
      have h2 : |((u : ℤ) : ℝ) * ((ℓ w : ℤ) : ℝ)| ≤ δ * u * (2 * (y : ℝ) ^ 2) + u / 2 := by
        rw [e']
        exact (abs_sub _ _).trans (add_le_add (htwb w hw) hs')
      rw [abs_mul] at h2
      push_cast at h2
      rw [abs_of_pos hu0] at h2
      nlinarith
    have h2 : |((ℓ w : ℤ) : ℝ)| ≤ 2 * δ * (y : ℝ) ^ 2 + 1 / 2 := le_of_mul_le_mul_left h1 hu0
    have h3 : (ℓ w).natAbs ≤ m := by
      apply Nat.le_floor
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact h2
    rw [Finset.mem_Icc]
    constructor <;> omega
  -- Step 3: each value of `ℓ` accounts for at most 5 primes `w`.
  have hfib : ∀ l : ℤ, (I.filter (fun w => ℓ w = l)).card ≤ 5 := by
    intro l
    by_contra hcon
    push_neg at hcon
    set T := I.filter (fun w => ℓ w = l) with hT
    obtain ⟨w0, hw0⟩ : T.Nonempty := Finset.card_pos.1 (by omega)
    have hw0I := (Finset.mem_filter.1 hw0).1
    have hw0l := (Finset.mem_filter.1 hw0).2
    set n : ℤ := s' + u * l with hn
    have hn0 : n ≠ 0 := by
      intro h
      apply hs'nd
      exact ⟨-l, by linarith⟩
    -- every `w ∈ T` divides `n`
    have hdvd : ∀ w ∈ T, w ∣ n.natAbs := by
      intro w hw
      have hwI := (Finset.mem_filter.1 hw).1
      have hwl := (Finset.mem_filter.1 hw).2
      have e := hℓeq w hwI
      rw [hwl] at e
      have : (w : ℤ) ∣ n := ⟨tw w, by rw [hn, ← e]; ring⟩
      exact Int.natCast_dvd.1 this
    -- `|n| ≤ y^{11}`
    have hnb : n.natAbs ≤ y ^ 11 := by
      have e := hℓeq w0 hw0I
      rw [hw0l] at e
      have h1 := htwb w0 hw0I
      rw [e] at h1
      have h2 : |(n : ℝ)| ≤ (y : ℝ) ^ 11 := by
        have : δ * u * (2 * (y : ℝ) ^ 2) ≤ (y : ℝ) ^ 11 := by
          have : δ * u * (2 * (y : ℝ) ^ 2) = (2 * δ) * (u * (y : ℝ) ^ 2) := by ring
          rw [this]
          have h3 : u * (y : ℝ) ^ 2 ≤ (y : ℝ) ^ 11 := by
            have : (y : ℝ) ^ 11 = (y : ℝ) ^ 9 * (y : ℝ) ^ 2 := by ring
            rw [this]
            exact mul_le_mul_of_nonneg_right huy9 (by positivity)
          calc 2 * δ * (u * (y : ℝ) ^ 2) ≤ 1 * (u * (y : ℝ) ^ 2) :=
                mul_le_mul_of_nonneg_right hδ1 (by positivity)
            _ ≤ (y : ℝ) ^ 11 := by linarith
        push_cast [hn] at h1 ⊢
        linarith
      have : ((n.natAbs : ℕ) : ℝ) ≤ ((y ^ 11 : ℕ) : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]; push_cast; exact h2
      exact_mod_cast this
    -- the product of the primes in `T` divides `n`, hence is at most `y^{11}`
    have hprod : ∏ w ∈ T, w ∣ n.natAbs :=
      Finset.prod_primes_dvd _ (fun w hw => (hWb w (Finset.mem_filter.1 hw).1).2.2.prime) hdvd
    have hprodle : ∏ w ∈ T, w ≤ y ^ 11 :=
      (Nat.le_of_dvd (Int.natAbs_pos.2 hn0) hprod).trans hnb
    -- but it exceeds `(y²)^6 = y^{12}`
    have hlow : (y ^ 2 + 1) ^ T.card ≤ ∏ w ∈ T, w :=
      Finset.pow_card_le_prod _ _ _ (fun w hw => (hWb w (Finset.mem_filter.1 hw).1).1)
    have h6 : (y ^ 2 + 1) ^ 6 ≤ (y ^ 2 + 1) ^ T.card :=
      Nat.pow_le_pow_right (by positivity) hcon
    have h12 : y ^ 11 < (y ^ 2 + 1) ^ 6 := by
      calc y ^ 11 < y ^ 12 := Nat.pow_lt_pow_right (by omega) (by norm_num)
        _ = (y ^ 2) ^ 6 := by ring
        _ < (y ^ 2 + 1) ^ 6 := Nat.pow_lt_pow_left (by omega) (by norm_num)
    omega
  -- Step 4: combine.
  have hcard : I.card ≤ 5 * (I.image ℓ).card :=
    Finset.card_le_mul_card_image I 5 (fun b _ => hfib b)
  have himg : (I.image ℓ).card ≤ 2 * m + 1 := by
    have h1 : I.image ℓ ⊆ Finset.Icc (-(m : ℤ)) m := by
      intro l hl
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hl
      exact hℓm w hw
    have h2 := Finset.card_le_card h1
    rw [Int.card_Icc] at h2
    omega
  have hmR : (m : ℝ) ≤ 2 * δ * (y : ℝ) ^ 2 + 1 / 2 := Nat.floor_le (by positivity)
  refine ⟨?_, ?_⟩
  · have : (I.card : ℝ) ≤ 5 * (2 * m + 1) := by exact_mod_cast (hcard.trans (by omega))
    linarith
  · have hW := hL.card_W
    have hc := hL.count
    have e : 5 * (4 * δ * (y : ℝ) ^ 2 + 2) = (y : ℝ) ^ 2 / (20 * Real.log y) + 10 := by
      rw [hδdef, delta]; field_simp; ring
    have e2 : (y : ℝ) ^ 2 / (16 * Real.log y) = ((y : ℝ) ^ 2 / (8 * Real.log y)) / 2 := by
      field_simp; ring
    rw [e]
    linarith

/-- The heart of the separation argument: in a *visible* row `w` (i.e. `‖s w̄/u‖ > δ` with
`s = ζ_u - ζ_u'`), the two phases cannot both be close to an integer:
`‖φ_{wu}(ξ,ζ_u)‖ + ‖φ_{wu}(ξ,ζ_u')‖ > δ` (triangle inequality for `‖·‖` and eq. (5)). -/
lemma visible_phase_sum (hL : Large τ y) {u w : ℕ} (hu : u ∈ Uset y Y) (hw : w ∈ Wset y)
    (ξ z z' : ℕ) (hvis : ¬ Invisible (delta y) u ((z : ℤ) - z') w) :
    delta y < nint (phase τ y u w ξ z) + nint (phase τ y u w ξ z') := by
  by_contra hcon
  push_neg at hcon
  apply hvis
  obtain ⟨k, hk, hph⟩ := eq_pf hL hu (Wset_subset_Vset hw) ξ z z'
  have h1 : nint ((k : ℝ) / u) ≤ delta y := by
    rw [← hph]; exact (nint_sub_le _ _).trans hcon
  obtain ⟨n, hn⟩ := exists_int_of_nint_le h1
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (prime_of_mem_Uset hu).pos
  refine ⟨k - n * u, ?_, ?_⟩
  · have e : ((k - n * u : ℤ) : ℝ) = u * ((k : ℝ) / u - n) := by push_cast; field_simp
    rw [e, abs_mul, abs_of_pos hu0, mul_comm]
    exact mul_le_mul_of_nonneg_right hn hu0.le
  · have e : (k - n * u) * (w : ℤ) - ((z : ℤ) - z') = ((w : ℤ) * k - ((z : ℤ) - z')) - u * (n * w) := by
      ring
    rw [e]
    exact dvd_sub hk (dvd_mul_right _ _)

/-- A product of factors in `[0,1]` only grows when factors are dropped. -/
lemma prod_le_prod_subset_of_le_one {s t : Finset ℕ} (hst : s ⊆ t) (f : ℕ → ℝ)
    (h0 : ∀ i ∈ t, 0 ≤ f i) (h1 : ∀ i ∈ t, f i ≤ 1) : ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i :=
  Finset.prod_le_prod_of_subset_of_le_one hst h0 (fun i hi _ => h1 i hi)

/-- The visible rows form at least half of `W` (Lemma 8.2). -/
lemma card_visible (hL : Large τ y) (hY : Y ≤ y ^ 9) {u : ℕ} (hu : u ∈ Uset y Y) {s : ℤ}
    (hs : ¬ (u : ℤ) ∣ s) :
    ((Wset y).card : ℝ) / 2 ≤
      (((Wset y).filter (fun w => ¬ Invisible (delta y) u s w)).card : ℝ) := by
  have h := lem_count hL hY hu hs
  have e := Finset.card_filter_add_card_filter_not
    (s := Wset y) (fun w => Invisible (delta y) u s w)
  have e' : (((Wset y).filter (fun w => Invisible (delta y) u s w)).card : ℝ) +
      (((Wset y).filter (fun w => ¬ Invisible (delta y) u s w)).card : ℝ) = (Wset y).card := by
    exact_mod_cast e
  linarith [h.1, h.2]

/-- `exp(-δ²/2)^{#visible} ≤ ε²`. -/
lemma pow_visible_le (n : ℕ) (hn : ((Wset y).card : ℝ) / 2 ≤ n) :
    exp (-(delta y ^ 2 / 2)) ^ n ≤ eps y ^ 2 := by
  rw [← Real.exp_nat_mul, eps, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  have : 0 ≤ delta y ^ 2 := by positivity
  push_cast
  nlinarith

/-- **Lemma 8.3 (Separation).**  Let `u ∈ U`, `ξ` row labels, and `ζ_u ≢ ζ_u' (mod u)`.
(i) `F_u(ξ,ζ_u) F_u(ξ,ζ_u') ≤ ε²`; in particular at most one label is heavy (`> ε`).
(ii) If `‖φ_{wu}(ξ, ζ_u')‖ ≤ δ/2` for all `w ∈ W`, then `F_u(ξ, ζ_u) ≤ ε`. -/
theorem lem_unique (hL : Large τ y) (hY : Y ≤ y ^ 9) {u : ℕ} (hu : u ∈ Uset y Y) (ξ z z' : ℕ)
    (hzz : ¬ (u : ℤ) ∣ (z : ℤ) - z') :
    Fcol τ y u ξ z * Fcol τ y u ξ z' ≤ eps y ^ 2 ∧
      ((∀ w ∈ Wset y, nint (phase τ y u w ξ z') ≤ delta y / 2) → Fcol τ y u ξ z ≤ eps y) := by
  set s : ℤ := (z : ℤ) - z' with hsdef
  set Vis := (Wset y).filter (fun w => ¬ Invisible (delta y) u s w) with hVis
  have hVisW : Vis ⊆ Wset y := Finset.filter_subset _ _
  have hVisV : Vis ⊆ Vset τ y := hVisW.trans Wset_subset_Vset
  have hcard := card_visible hL hY hu hzz
  -- one cosine factor is at most `exp(-δ²/2)` when its phase exceeds `δ/2`
  have hfac : ∀ x : ℝ, delta y / 2 < nint x → |Real.cos (π * x)| ≤ exp (-(delta y ^ 2 / 2)) := by
    intro x hx
    refine (lem_cos x).trans (Real.exp_le_exp.2 ?_)
    have : 0 ≤ delta y / 2 := by
      have := hL.y_ge
      rw [delta]
      have : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
      positivity
    nlinarith
  set c := fun (ζ : ℕ) (v : ℕ) => |Real.cos (π * phase τ y u v ξ ζ)| with hc
  have hc0 : ∀ ζ v, 0 ≤ c ζ v := fun _ _ => abs_nonneg _
  have hc1 : ∀ ζ v, c ζ v ≤ 1 := fun _ _ => Real.abs_cos_le_one _
  constructor
  · -- (i)
    have e : Fcol τ y u ξ z * Fcol τ y u ξ z' = ∏ v ∈ Vset τ y, (c z v * c z' v) := by
      rw [Fcol, Fcol, ← Finset.prod_mul_distrib]
    rw [e]
    calc ∏ v ∈ Vset τ y, (c z v * c z' v) ≤ ∏ v ∈ Vis, (c z v * c z' v) :=
          prod_le_prod_subset_of_le_one hVisV _ (fun v _ => mul_nonneg (hc0 _ _) (hc0 _ _))
            (fun v _ => mul_le_one₀ (hc1 _ _) (hc0 _ _) (hc1 _ _))
      _ ≤ ∏ v ∈ Vis, exp (-(delta y ^ 2 / 2)) := by
          apply Finset.prod_le_prod (fun v _ => mul_nonneg (hc0 _ _) (hc0 _ _))
          intro w hw
          have hw' := Finset.mem_filter.1 hw
          have hsum := visible_phase_sum hL hu hw'.1 ξ z z' hw'.2
          by_cases h1 : delta y / 2 < nint (phase τ y u w ξ z)
          · calc c z w * c z' w ≤ exp (-(delta y ^ 2 / 2)) * 1 :=
                  mul_le_mul (hfac _ h1) (hc1 _ _) (hc0 _ _) (by positivity)
              _ = _ := mul_one _
          · have h2 : delta y / 2 < nint (phase τ y u w ξ z') := by linarith
            calc c z w * c z' w ≤ 1 * exp (-(delta y ^ 2 / 2)) :=
                  mul_le_mul (hc1 _ _) (hfac _ h2) (hc0 _ _) zero_le_one
              _ = _ := one_mul _
      _ = exp (-(delta y ^ 2 / 2)) ^ Vis.card := Finset.prod_const _
      _ ≤ eps y ^ 2 := pow_visible_le _ hcard
  · -- (ii)
    intro hsmall
    have heps1 : eps y ≤ 1 := by
      rw [eps]; apply Real.exp_le_one_iff.2
      have : 0 ≤ ((Wset y).card : ℝ) * delta y ^ 2 / 8 := by positivity
      linarith
    have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
    calc Fcol τ y u ξ z = ∏ v ∈ Vset τ y, c z v := rfl
      _ ≤ ∏ v ∈ Vis, c z v := prod_le_prod_subset_of_le_one hVisV _ (fun v _ => hc0 _ _)
            (fun v _ => hc1 _ _)
      _ ≤ ∏ v ∈ Vis, exp (-(delta y ^ 2 / 2)) := by
          apply Finset.prod_le_prod (fun v _ => hc0 _ _)
          intro w hw
          have hw' := Finset.mem_filter.1 hw
          have hsum := visible_phase_sum hL hu hw'.1 ξ z z' hw'.2
          have h2 := hsmall w hw'.1
          exact hfac _ (by linarith)
      _ = exp (-(delta y ^ 2 / 2)) ^ Vis.card := Finset.prod_const _
      _ ≤ eps y ^ 2 := pow_visible_le _ hcard
      _ ≤ eps y := by nlinarith

/-- Consequence of Lemma 8.3(i): at most one label of a column is heavy. -/
lemma heavy_unique (hL : Large τ y) (hY : Y ≤ y ^ 9) {u : ℕ} (hu : u ∈ Uset y Y) (ξ z z' : ℕ)
    (hz : eps y < Fcol τ y u ξ z) (hz' : eps y < Fcol τ y u ξ z') : (u : ℤ) ∣ (z : ℤ) - z' := by
  by_contra hcon
  have h := (lem_unique hL hY hu ξ z z' hcon).1
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  have : eps y * eps y < Fcol τ y u ξ z * Fcol τ y u ξ z' :=
    mul_lt_mul'' hz hz' heps0 heps0
  nlinarith

/-- **Lemma 8.4 (No wrap-around).**  Let `u ∈ U`, `ξ` row labels and `ζ_u` a column label.
If `‖φ_{vu}(ξ, ζ_u)‖ ≤ δ_a` for all `v ∈ V`, then there is an integer `M` with `|M| ≤ y^7/4`
and `ξ ≡ M (mod v)` for all `v ∈ V`; in particular `ξ` is coherent. -/
theorem lem_admissible (hL : Large τ y) (hY : Y ≤ y ^ 9) {u : ℕ} (hu : u ∈ Uset y Y) (ξ z : ℕ)
    (h : ∀ v ∈ Vset τ y, nint (phase τ y u v ξ z) ≤ deltaA y) :
    ∃ M : ℤ, (|M| : ℝ) ≤ (y : ℝ) ^ 7 / 4 ∧ ∀ v ∈ Vset τ y, (v : ℤ) ∣ (ξ : ℤ) - M := by
  set J : ℤ := ((crt τ y u ξ z : ℕ) : ℤ) with hJdef
  obtain ⟨hu8, huY, hup⟩ := mem_Uset.1 hu
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hup.pos
  have hy0 : (0 : ℝ) < y := by have := hL.y_ge; exact_mod_cast (by omega : 0 < y)
  -- `J_v`: the balanced representative of `J` modulo `uv`
  let Jv : ℕ → ℤ := fun v => J - round ((J : ℝ) / ((u : ℝ) * v)) * (u * v)
  have hJv_bound : ∀ v ∈ Vset τ y, |((Jv v : ℤ) : ℝ)| ≤ deltaA y * u * v := by
    intro v hv
    have hv0 : (0 : ℝ) < v := by exact_mod_cast (prime_of_mem_Vset hv).pos
    have h1 := h v hv
    unfold nint phase at h1
    have e : ((Jv v : ℤ) : ℝ) = ((u : ℝ) * v) *
        ((J : ℝ) / ((u : ℝ) * v) - round ((J : ℝ) / ((u : ℝ) * v))) := by
      simp only [Jv]; push_cast; field_simp
    rw [e, abs_mul, abs_of_pos (by positivity)]
    have hJ : ((crt τ y u ξ z : ℕ) : ℝ) = (J : ℝ) := by rw [hJdef]; push_cast; rfl
    rw [hJ] at h1
    have : (0 : ℝ) < u * v := by positivity
    calc (u : ℝ) * v * |(J : ℝ) / ((u : ℝ) * v) - round ((J : ℝ) / ((u : ℝ) * v))|
        ≤ u * v * deltaA y := mul_le_mul_of_nonneg_left h1 this.le
      _ = deltaA y * u * v := by ring
  have hJv_u : ∀ v ∈ Vset τ y, |((Jv v : ℤ) : ℝ)| ≤ u / 4 := by
    intro v hv
    have hvb := (le_of_mem_Vset hL hv).2
    have hvR : (v : ℝ) ≤ 2 * (y : ℝ) ^ 2 := by exact_mod_cast hvb
    refine (hJv_bound v hv).trans ?_
    rw [deltaA]
    have : 1 / (8 * (y : ℝ) ^ 2) * u * v = u * (v / (8 * (y : ℝ) ^ 2)) := by ring
    rw [this]
    have : v / (8 * (y : ℝ) ^ 2) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    nlinarith
  -- all `J_v` are `≡ J (mod u)`, differ by less than `u`, hence are equal
  have hJv_mod : ∀ v, (u : ℤ) ∣ J - Jv v := by
    intro v; exact ⟨round ((J : ℝ) / ((u : ℝ) * v)) * v, by simp only [Jv]; ring⟩
  have h2 : (2 : ℕ) ∈ Vset τ y := two_mem_Vset
  have hall : ∀ v ∈ Vset τ y, Jv v = Jv 2 := by
    intro v hv
    have hd : (u : ℤ) ∣ Jv v - Jv 2 := by
      have := dvd_sub (hJv_mod 2) (hJv_mod v)
      have e : J - Jv 2 - (J - Jv v) = Jv v - Jv 2 := by ring
      rwa [e] at this
    have hlt : |Jv v - Jv 2| < (u : ℤ) := by
      have h1 := hJv_u v hv
      have h2' := hJv_u 2 h2
      have : |((Jv v - Jv 2 : ℤ) : ℝ)| < (u : ℝ) := by
        push_cast
        calc |((Jv v : ℤ) : ℝ) - ((Jv 2 : ℤ) : ℝ)| ≤ |((Jv v : ℤ) : ℝ)| + |((Jv 2 : ℤ) : ℝ)| :=
              abs_sub _ _
          _ ≤ u / 4 + u / 4 := add_le_add h1 h2'
          _ < u := by linarith
      exact_mod_cast this
    have := Int.eq_zero_of_abs_lt_dvd hd hlt
    linarith
  refine ⟨Jv 2, ?_, ?_⟩
  · -- `|M| = |J_2| ≤ 2 δ_a u ≤ Y/(4y²) ≤ y^7/4`
    have h1 := hJv_bound 2 h2
    have huy : (u : ℝ) ≤ (y : ℝ) ^ 9 := by exact_mod_cast huY.trans hY
    push_cast at h1 ⊢
    calc |((Jv 2 : ℤ) : ℝ)| ≤ deltaA y * u * 2 := h1
      _ = u / (4 * (y : ℝ) ^ 2) := by rw [deltaA]; field_simp; ring
      _ ≤ (y : ℝ) ^ 9 / (4 * (y : ℝ) ^ 2) := by gcongr
      _ = (y : ℝ) ^ 7 / 4 := by field_simp
  · -- `M = J_v ≡ J ≡ ξ (mod v)`
    intro v hv
    rw [← hall v hv]
    have hvP : (v : ℤ) ∣ (PV τ y : ℤ) := by
      exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hv
    have hJξ : (v : ℤ) ∣ (ξ : ℤ) - J := hvP.trans (crt_modEq_xi hL hu ξ z).dvd
    have : (ξ : ℤ) - Jv v = ((ξ : ℤ) - J) + round ((J : ℝ) / ((u : ℝ) * v)) * u * v := by
      simp only [Jv]; ring
    rw [this]
    exact dvd_add hJξ (dvd_mul_left _ _)

/-- Lemma 8.4, last sentence: under its hypothesis the row labels `ξ` are coherent. -/
lemma coherent_of_admissible (hL : Large τ y) (hY : Y ≤ y ^ 9) {u : ℕ} (hu : u ∈ Uset y Y)
    (ξ z : ℕ) (h : ∀ v ∈ Vset τ y, nint (phase τ y u v ξ z) ≤ deltaA y) :
    Coherent τ y ξ := by
  obtain ⟨M, hM, hMv⟩ := lem_admissible hL hY hu ξ z h
  refine ⟨M, ?_, hMv⟩
  have : ((|M| : ℤ) : ℝ) ≤ ((y ^ 7 : ℕ) : ℤ) := by
    push_cast
    have : (0 : ℝ) ≤ (y : ℝ) ^ 7 := by positivity
    linarith
  exact_mod_cast this

end Erdos306
