/-
§5 of the paper: counting with a geometric sum.

For a finite edge set `A` (pairs `(v,u)`, the edge standing for `1/(vu)`), a target `τ` and a
common denominator `L`, the number `N` of subsets `S ⊆ A` with `σ(S) ≡ τ (mod 1)` satisfies
  `N / 2^{|A|} = (1/L) ∑_h e(-hτ) φ(h)`,       eq. (2)
where `h` runs over the frequencies `-L/2 < h ≤ L/2` and `φ(h) = ∏_{(v,u)∈A} (1 + e(h/(uv)))/2`.
-/
import Erdos306.Construction

namespace Erdos306

open Real Finset

/-- The frequencies: the integers `h` with `-⌊L/2⌋ < h ≤ L - ⌊L/2⌋` (for even `L`, exactly the
paper's `-L/2 < h ≤ L/2`); a complete residue system modulo `L`. -/
noncomputable def freq (L : ℕ) : Finset ℤ := Finset.Ioc (-((L : ℤ) / 2)) ((L : ℤ) - (L : ℤ) / 2)

/-- `φ(h) = ∏_{(v,u) ∈ A} (1 + e(h/(uv)))/2`. -/
noncomputable def phi (A : Finset (ℕ × ℕ)) (h : ℤ) : ℂ :=
  ∏ p ∈ A, (1 + ee ((h : ℝ) / ((p.1 : ℝ) * p.2))) / 2

open Classical in
/-- `N`: the number of `S ⊆ A` with `σ(S) ≡ τ (mod 1)`. -/
noncomputable def Ncount (A : Finset (ℕ × ℕ)) (τ : ℚ) : ℕ :=
  ((A.powerset).filter (fun S => ∃ k : ℤ, sigma S - τ = k)).card

/-- There are exactly `L` frequencies. -/
lemma card_freq (L : ℕ) : (freq L).card = L := by
  simp [freq]

/-- `e(n) = 1` for integers `n` (period 1). -/
lemma ee_int (n : ℤ) : ee (n : ℝ) = 1 := by
  unfold ee
  rw [← Complex.exp_int_mul_two_pi_mul_I n]
  congr 1; push_cast; ring

/-- `e(kx) = e(x)^k`. -/
lemma ee_nat_mul (k : ℕ) (x : ℝ) : ee ((k : ℝ) * x) = ee x ^ k := by
  unfold ee
  rw [← Complex.exp_nat_mul]
  congr 1; push_cast; ring

/-- `e(∑ f) = ∏ e(f)`. -/
lemma ee_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) : ee (∑ i ∈ s, f i) = ∏ i ∈ s, ee (f i) := by
  unfold ee
  rw [← Complex.exp_sum]
  congr 1; push_cast; rw [Finset.mul_sum]

/-- `e(x) = 1` iff `x` is an integer. -/
lemma ee_eq_one_iff (x : ℝ) : ee x = 1 ↔ ∃ n : ℤ, x = n := by
  unfold ee
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : ((x : ℂ) - n) * (2 * π * Complex.I) = 0 := by rw [sub_mul]; rw [← hn]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact_mod_cast sub_eq_zero.1 h
    · exact absurd h hpi
  · rintro ⟨n, rfl⟩; exact ⟨n, by push_cast; ring⟩

/-- The geometric-series identity: over any `L` consecutive integers `h`,
`∑_h e(hm/L) = L` if `L ∣ m` and `= 0` otherwise. -/
theorem lem_geom (L : ℕ) (hL : 0 < L) (a m : ℤ) :
    ∑ h ∈ Finset.Ioc a (a + L), ee ((h : ℝ) * m / L) = if (L : ℤ) ∣ m then (L : ℂ) else 0 := by
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  split_ifs with hdvd
  · obtain ⟨k, rfl⟩ := hdvd
    have : ∀ h ∈ Finset.Ioc a (a + L), ee ((h : ℝ) * ((L : ℤ) * k : ℤ) / L) = 1 := by
      intro h _
      have : (h : ℝ) * (((L : ℤ) * k : ℤ) : ℝ) / L = ((h * k : ℤ) : ℝ) := by
        push_cast; field_simp
      rw [this, ee_int]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Int.card_Ioc]
    simp
  · -- reindex `h = a + 1 + k`, `0 ≤ k < L`
    have hre : ∑ h ∈ Finset.Ioc a (a + L), ee ((h : ℝ) * m / L) =
        ∑ k ∈ Finset.range L, ee (((a + 1 : ℤ) : ℝ) * m / L) * ee ((m : ℝ) / L) ^ k := by
      refine Finset.sum_nbij' (fun h => (h - a - 1).toNat) (fun k => a + 1 + k) ?_ ?_ ?_ ?_ ?_
      · intro h hh; simp only [Finset.mem_Ioc] at hh; simp only [Finset.mem_range]; omega
      · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Ioc]; omega
      · intro h hh; simp only [Finset.mem_Ioc] at hh
        show a + 1 + ((h - a - 1).toNat : ℤ) = h; omega
      · intro k _
        show (a + 1 + (k : ℤ) - a - 1).toNat = k; omega
      · intro h hh
        simp only [Finset.mem_Ioc] at hh
        rw [← ee_nat_mul, ← ee_add]
        congr 1
        have : (((h - a - 1).toNat : ℕ) : ℝ) = (h : ℝ) - a - 1 := by
          have : (((h - a - 1).toNat : ℕ) : ℤ) = h - a - 1 := Int.toNat_of_nonneg (by omega)
          exact_mod_cast this
        rw [this]; push_cast; field_simp; ring
    rw [hre, ← Finset.mul_sum]
    set ζ := ee ((m : ℝ) / L)
    have hζ1 : ζ ≠ 1 := by
      intro h
      obtain ⟨n, hn⟩ := (ee_eq_one_iff _).1 h
      apply hdvd
      refine ⟨n, ?_⟩
      have : (m : ℝ) = L * n := by field_simp at hn; linarith
      exact_mod_cast this
    have hζL : ζ ^ L = 1 := by
      rw [← ee_nat_mul]
      have : (L : ℝ) * ((m : ℝ) / L) = ((m : ℤ) : ℝ) := by field_simp
      rw [this, ee_int]
    rw [geom_sum_eq hζ1, hζL]
    simp

/-- **Formula (2)**: `N / 2^{|A|} = (1/L) ∑_h e(-hτ) φ(h)`, valid whenever `L > 0`, every
edge `vu` divides `L`, and the denominator of `τ` divides `L`. -/
theorem eq_N (A : Finset (ℕ × ℕ)) (τ : ℚ) (L : ℕ) (hL : 0 < L)
    (hA : ∀ p ∈ A, 0 < p.1 * p.2 ∧ p.1 * p.2 ∣ L) (hτ : τ.den ∣ L) :
    (Ncount A τ : ℂ) / 2 ^ A.card =
      (1 / (L : ℂ)) * ∑ h ∈ freq L, ee (-((h : ℝ) * τ)) * phi A h := by
  classical
  have hLq : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  -- every `L (σ(S) - τ)` is an integer
  have hint : ∀ S ⊆ A, ∃ m : ℤ, (L : ℚ) * (sigma S - τ) = m := by
    intro S hS
    have hσ : ∃ m : ℤ, (L : ℚ) * sigma S = m := by
      induction S using Finset.induction_on with
      | empty => exact ⟨0, by simp [sigma]⟩
      | insert p S hpS ih =>
        obtain ⟨m, hm⟩ := ih ((Finset.subset_insert _ _).trans hS)
        obtain ⟨hpos, ⟨c, hc⟩⟩ := hA p (hS (Finset.mem_insert_self _ _))
        refine ⟨c + m, ?_⟩
        unfold sigma at hm ⊢
        rw [Finset.sum_insert hpS, mul_add, hm, hc]
        have : ((p.1 : ℚ) * p.2) ≠ 0 := by exact_mod_cast hpos.ne'
        push_cast
        rw [mul_one_div, mul_div_cancel_left₀ _ this]
    obtain ⟨m, hm⟩ := hσ
    obtain ⟨c, hc⟩ := hτ
    refine ⟨m - c * τ.num, ?_⟩
    rw [mul_sub, hm]
    push_cast
    congr 1
    conv_lhs => rw [← Rat.num_div_den τ, hc]
    have : (τ.den : ℚ) ≠ 0 := by exact_mod_cast τ.den_pos.ne'
    push_cast
    field_simp
  -- the indicator of `σ(S) ≡ τ` as a geometric sum
  have hind : ∀ S ⊆ A, (if ∃ k : ℤ, sigma S - τ = k then (1 : ℂ) else 0) =
      (1 / (L : ℂ)) * ∑ h ∈ freq L, ee ((h : ℝ) * (((sigma S : ℚ) : ℝ) - τ)) := by
    intro S hS
    obtain ⟨m, hm⟩ := hint S hS
    have hσq : sigma S - τ = (m : ℚ) / L := by
      rw [eq_div_iff hLq, mul_comm, hm]
    have hσ : (((sigma S : ℚ) : ℝ) - τ) = (m : ℝ) / L := by
      have := congrArg (fun q : ℚ => (q : ℝ)) hσq
      push_cast at this
      exact this
    have hsum : ∑ h ∈ freq L, ee ((h : ℝ) * (((sigma S : ℚ) : ℝ) - τ)) =
        if (L : ℤ) ∣ m then (L : ℂ) else 0 := by
      rw [← lem_geom L hL (-((L : ℤ) / 2)) m]
      unfold freq
      have : (L : ℤ) - (L : ℤ) / 2 = -((L : ℤ) / 2) + L := by ring
      rw [this]
      refine Finset.sum_congr rfl (fun h _ => ?_)
      rw [hσ]; ring_nf
    rw [hsum]
    have hiff : (∃ k : ℤ, sigma S - τ = k) ↔ (L : ℤ) ∣ m := by
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have : (m : ℚ) = L * k := by rw [← hm, hk]
        exact_mod_cast this
      · rintro ⟨c, hc⟩
        refine ⟨c, ?_⟩
        rw [hσq, hc]; push_cast; field_simp
    by_cases hc : (L : ℤ) ∣ m
    · rw [if_pos hc, if_pos (hiff.2 hc)]
      have : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      field_simp
    · rw [if_neg hc, if_neg (mt hiff.1 hc)]; simp
  -- the product formula for `φ`
  have hphi : ∀ h : ℤ, ee (-((h : ℝ) * τ)) * phi A h =
      (1 / 2 ^ A.card) * ∑ S ∈ A.powerset, ee ((h : ℝ) * (((sigma S : ℚ) : ℝ) - τ)) := by
    intro h
    have h1 : phi A h = (∏ p ∈ A, (1 + ee ((h : ℝ) / ((p.1 : ℝ) * p.2)))) / 2 ^ A.card := by
      unfold phi; rw [Finset.prod_div_distrib, Finset.prod_const]
    have h2 : ∏ p ∈ A, (1 + ee ((h : ℝ) / ((p.1 : ℝ) * p.2))) =
        ∑ S ∈ A.powerset, ee ((h : ℝ) * ((sigma S : ℚ) : ℝ)) := by
      have := Finset.prod_add (fun p : ℕ × ℕ => ee ((h : ℝ) / ((p.1 : ℝ) * p.2)))
        (fun _ => (1 : ℂ)) A
      simp only [Finset.prod_const_one, mul_one] at this
      rw [Finset.prod_congr rfl (fun p _ => add_comm _ _), this]
      refine Finset.sum_congr rfl (fun S _ => ?_)
      rw [← ee_sum]
      congr 1
      unfold sigma; push_cast; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_); ring
    rw [h1, h2, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [show (h : ℝ) * (((sigma S : ℚ) : ℝ) - τ) = -((h : ℝ) * τ) + (h : ℝ) * ((sigma S : ℚ) : ℝ)
      by ring, ee_add]
    ring
  rw [Finset.sum_congr rfl (fun h _ => hphi h)]
  unfold Ncount
  rw [Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_congr rfl (fun S hS => hind S (Finset.mem_powerset.1 hS))]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  ring

/-- eq. (3): `1 + e(x) = 2 e(x/2) cos πx`. -/
lemma eq_half (x : ℝ) : 1 + ee x = 2 * ee (x / 2) * (Real.cos (π * x) : ℂ) := by
  rw [mul_assoc, mul_comm (ee _), ← mul_assoc, Complex.ofReal_cos, Complex.two_cos]
  unfold ee
  rw [add_mul, ← Complex.exp_add, ← Complex.exp_add]
  have e1 : (↑(π * x) : ℂ) * Complex.I + 2 * ↑π * Complex.I * ↑(x / 2) = 2 * π * Complex.I * x := by
    push_cast; ring
  have e2 : -(↑(π * x) : ℂ) * Complex.I + 2 * ↑π * Complex.I * ↑(x / 2) = 0 := by
    push_cast; ring
  rw [e1, e2, Complex.exp_zero, add_comm]

/-- `|φ(h)| = ∏_{(v,u) ∈ A} |cos(π h/(uv))|`. -/
lemma norm_phi (A : Finset (ℕ × ℕ)) (h : ℤ) :
    ‖phi A h‖ = ∏ p ∈ A, |Real.cos (π * ((h : ℝ) / ((p.1 : ℝ) * p.2)))| := by
  unfold phi
  rw [norm_prod]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [eq_half, norm_div, norm_mul, norm_mul, norm_ee, Complex.norm_real, Real.norm_eq_abs]
  simp

/-- Each factor of `φ(h)` has absolute value at most `1`, so `|φ(h)| ≤ 1` (§5). -/
lemma norm_phi_le_one (A : Finset (ℕ × ℕ)) (h : ℤ) : ‖phi A h‖ ≤ 1 := by
  rw [norm_phi]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => Real.abs_cos_le_one _)

/-- `φ(0) = 1` (§5). -/
lemma phi_zero (A : Finset (ℕ × ℕ)) : phi A 0 = 1 := by
  simp [phi, ee]

end Erdos306
