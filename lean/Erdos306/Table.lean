/-
§6 of the paper: the `V × U` table and the three cases.

By the Chinese remainder theorem a frequency `h` is the same as its row labels
`ξ_v = h mod v` (`v ∈ V`) and its column labels `ζ_u = h mod u` (`u ∈ U`).  We record the row
labels as a single residue `ξ = h mod P_V`, `P_V = ∏_{v∈V} v` (so `ξ_v = ξ mod v`), and the
column labels as residues `ζ_u ∈ [0, u)`.  The `(v,u)` entry of the table is
`|cos π φ_{vu}|`, where the phase `φ_{vu}(ξ, ζ_u) = J/(uv)` for the CRT integer
`J ≡ ξ (mod P_V)`, `J ≡ ζ_u (mod u)`.

For the minor-arc bound we only need that the label map `h ↦ (ξ, ζ)` is *injective* on
frequencies (`label_inj`); surjectivity (the other half of the CRT bijection) is never used,
because all terms are nonnegative.
-/
import Erdos306.Counting

namespace Erdos306

open Real Finset

variable (τ : ℚ) (y Y : ℕ)

/-- `P_V = ∏_{v ∈ V} v = |G_V|`. -/
def PV : ℕ := ∏ v ∈ Vset τ y, v

/-- The CRT integer `J ∈ [0, P_V u)` with `J ≡ ξ (mod P_V)` and `J ≡ z (mod u)`. -/
noncomputable def crt (u ξ z : ℕ) : ℕ :=
  if h : Nat.Coprime (PV τ y) u then (Nat.chineseRemainder h ξ z).1 else 0

/-- The phase `φ_{vu}(ξ, ζ_u) = J/(uv)` (defined modulo 1; only `|cos π ·|` and `‖·‖` of it are
used). -/
noncomputable def phase (u v ξ z : ℕ) : ℝ := (crt τ y u ξ z : ℝ) / ((u : ℝ) * v)

/-- `F_u(ξ, ζ_u) = ∏_{v ∈ V} |cos π φ_{vu}(ξ, ζ_u)|`: the weight of column `u`. -/
noncomputable def Fcol (u ξ z : ℕ) : ℝ := ∏ v ∈ Vset τ y, |Real.cos (π * phase τ y u v ξ z)|

/-- `S_u(ξ) = ∑_{ζ_u mod u} F_u(ξ, ζ_u)`. -/
noncomputable def Scol (u ξ : ℕ) : ℝ := ∑ z ∈ range u, Fcol τ y u ξ z

/-- Row labels `ξ` are *coherent* if `ξ ≡ M (mod v)` for all `v ∈ V`, for some `|M| ≤ y^7`. -/
def Coherent (ξ : ℤ) : Prop := ∃ M : ℤ, |M| ≤ (y : ℤ) ^ 7 ∧ ∀ v ∈ Vset τ y, (v : ℤ) ∣ ξ - M

/-- Case I: coherent rows `ξ ≡ M`, all columns matching (`ζ_u ≡ M (mod u)` for all `u`). -/
def CaseI (h : ℤ) : Prop :=
  ∃ M : ℤ, |M| ≤ (y : ℤ) ^ 7 ∧ (∀ v ∈ Vset τ y, (v : ℤ) ∣ h - M) ∧ ∀ u ∈ Uset y Y, (u : ℤ) ∣ h - M

/-- Case II: coherent rows `ξ ≡ M`, some mismatched column. -/
def CaseII (h : ℤ) : Prop :=
  ∃ M : ℤ, |M| ≤ (y : ℤ) ^ 7 ∧ (∀ v ∈ Vset τ y, (v : ℤ) ∣ h - M) ∧
    ∃ u ∈ Uset y Y, ¬ (u : ℤ) ∣ h - M

/-- Case III: incoherent rows. -/
def CaseIII (h : ℤ) : Prop := ¬ Coherent τ y h

variable {τ y Y}

/-- A product of distinct primes that all divide an integer `n` divides `n`. -/
lemma prod_primes_dvd_int (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (n : ℤ)
    (h : ∀ p ∈ t, (p : ℤ) ∣ n) : ((∏ p ∈ t, p : ℕ) : ℤ) ∣ n := by
  apply Int.natCast_dvd.2
  exact Finset.prod_primes_dvd _ (fun p hp => (ht p hp).prime)
    (fun p hp => Int.natCast_dvd.1 (h p hp))

/-- `u > 2y² ≥ v` for `u ∈ U`, `v ∈ V`. -/
lemma v_lt_u (hL : Large τ y) {u v : ℕ} (hu : u ∈ Uset y Y) (hv : v ∈ Vset τ y) : v < u := by
  have h1 := (le_of_mem_Vset hL hv).2
  have h2 := (bounds_of_mem_Uset hu).1
  have hy := hL.y_ge
  have : 2 * y ^ 2 < y ^ 8 := by
    have : y ^ 8 = y ^ 2 * y ^ 6 := by ring
    have h6 : 2 < y ^ 6 := by
      calc 2 < 3 ^ 6 := by norm_num
        _ ≤ y ^ 6 := Nat.pow_le_pow_left hy 6
    rw [this]
    have : 0 < y ^ 2 := by positivity
    nlinarith
  omega

/-- For `v ∈ V` and `u ∈ U`: `P_V` and `u` are coprime. -/
lemma coprime_PV_u (hL : Large τ y) {u : ℕ} (hu : u ∈ Uset y Y) : Nat.Coprime (PV τ y) u := by
  apply Nat.Coprime.prod_left
  intro v hv
  exact (Nat.coprime_primes (prime_of_mem_Vset hv) (prime_of_mem_Uset hu)).2
    (v_lt_u hL hu hv).ne

/-- `|W| ≥ 100` (from eq. (1) and the numerical condition of Lemma 8.2). -/
lemma card_W_ge (hL : Large τ y) : 100 ≤ (Wset y).card := by
  have h1 := hL.card_W
  have h2 := hL.count
  have hy : (3 : ℝ) ≤ y := by exact_mod_cast hL.y_ge
  have hlog : 0 < Real.log y := Real.log_pos (by linarith)
  have e1 : (y : ℝ) ^ 2 / (16 * Real.log y) - (y : ℝ) ^ 2 / (20 * Real.log y) =
      ((y : ℝ) ^ 2 / (8 * Real.log y)) / 10 := by field_simp; ring
  have : (100 : ℝ) ≤ (Wset y).card := by linarith
  exact_mod_cast this

/-- `P_V > y^8`. -/
lemma PV_gt_y8 (hL : Large τ y) : y ^ 8 < PV τ y := by
  have hW := card_W_ge hL
  have h1 : ∏ w ∈ Wset y, w ≤ PV τ y := by
    unfold PV
    apply Finset.prod_le_prod_of_subset_of_one_le' Wset_subset_Vset
    intro v hv _
    exact (prime_of_mem_Vset hv).one_lt.le
  have h2 : (y ^ 2 + 1) ^ (Wset y).card ≤ ∏ w ∈ Wset y, w :=
    Finset.pow_card_le_prod _ _ _ (fun w hw => (mem_Wset.1 hw).1)
  have h3 : (y ^ 2 + 1) ^ 4 ≤ (y ^ 2 + 1) ^ (Wset y).card :=
    Nat.pow_le_pow_right (by positivity) (by omega)
  have h4 : y ^ 8 < (y ^ 2 + 1) ^ 4 := by
    calc y ^ 8 = (y ^ 2) ^ 4 := by ring
      _ < (y ^ 2 + 1) ^ 4 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  omega

/-- `P_V > 2 y^7` (so a coherent `ξ` determines `M`). -/
lemma PV_gt (hL : Large τ y) : 2 * (y : ℤ) ^ 7 < PV τ y := by
  have h := PV_gt_y8 hL
  have hy := hL.y_ge
  have : 2 * y ^ 7 < y ^ 8 := by
    have : y ^ 8 = y * y ^ 7 := by ring
    rw [this]
    have : 0 < y ^ 7 := by positivity
    nlinarith
  exact_mod_cast (by omega : 2 * y ^ 7 < PV τ y)

/-- `L > 2 y^7 + 2`. -/
lemma L_gt (hL : Large τ y) : 2 * (y : ℤ) ^ 7 + 2 < Lnum τ y Y := by
  have h := PV_gt_y8 hL
  have hy := hL.y_ge
  have h1 : PV τ y ≤ Lnum τ y Y := by
    unfold PV Lnum
    apply Finset.prod_le_prod_of_subset_of_one_le' Finset.subset_union_left
    intro p hp _
    rcases Finset.mem_union.1 hp with h | h
    · exact (prime_of_mem_Vset h).one_lt.le
    · exact (prime_of_mem_Uset h).one_lt.le
  have : 2 * y ^ 7 + 2 < y ^ 8 := by
    have : y ^ 8 = y * y ^ 7 := by ring
    rw [this]
    have : 3 ≤ y ^ 7 := le_trans hy (Nat.le_self_pow (by norm_num) y)
    nlinarith
  exact_mod_cast (by omega : 2 * y ^ 7 + 2 < Lnum τ y Y)

/-- The CRT integer is `≡ ξ (mod P_V)`. -/
lemma crt_modEq_xi (hL : Large τ y) {u : ℕ} (hu : u ∈ Uset y Y) (ξ z : ℕ) :
    ((crt τ y u ξ z : ℕ) : ℤ) ≡ ξ [ZMOD PV τ y] := by
  have hc := coprime_PV_u hL hu
  have h := (Nat.chineseRemainder hc ξ z).2.1
  unfold crt
  rw [dif_pos hc]
  exact Int.modEq_iff_dvd.2 (Nat.modEq_iff_dvd.1 h)

/-- The CRT integer is `≡ ζ_u (mod u)`. -/
lemma crt_modEq_z (hL : Large τ y) {u : ℕ} (hu : u ∈ Uset y Y) (ξ z : ℕ) :
    ((crt τ y u ξ z : ℕ) : ℤ) ≡ z [ZMOD u] := by
  have hc := coprime_PV_u hL hu
  have h := (Nat.chineseRemainder hc ξ z).2.2
  unfold crt
  rw [dif_pos hc]
  exact Int.modEq_iff_dvd.2 (Nat.modEq_iff_dvd.1 h)

/-- The phase depends only on `J` modulo `uv`: if `J ≡ ξ (mod v)` and `J ≡ z (mod u)` then
`|cos π φ_{vu}(ξ,z)| = |cos(π J/(uv))|` and `‖φ_{vu}(ξ,z)‖ = ‖J/(uv)‖`. -/
lemma phase_congr (hL : Large τ y) {u v : ℕ} (hu : u ∈ Uset y Y) (hv : v ∈ Vset τ y)
    (ξ z : ℕ) (J : ℤ) (hJv : (v : ℤ) ∣ J - ξ) (hJu : (u : ℤ) ∣ J - z) :
    ∃ n : ℤ, phase τ y u v ξ z = (J : ℝ) / ((u : ℝ) * v) + n := by
  set C : ℤ := ((crt τ y u ξ z : ℕ) : ℤ) with hC
  have hvP : (v : ℤ) ∣ (PV τ y : ℤ) := by
    exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hv
  have h1 : (v : ℤ) ∣ C - J := by
    have := hvP.trans (crt_modEq_xi hL hu ξ z).dvd
    have e : C - J = -(J - ξ) - ((ξ : ℤ) - C) := by ring
    rw [e]; exact dvd_sub (dvd_neg.2 hJv) this
  have h2 : (u : ℤ) ∣ C - J := by
    have := (crt_modEq_z hL hu ξ z).dvd
    have e : C - J = -(J - z) - ((z : ℤ) - C) := by ring
    rw [e]; exact dvd_sub (dvd_neg.2 hJu) this
  have hcop : IsCoprime (u : ℤ) (v : ℤ) := Nat.isCoprime_iff_coprime.2
    ((Nat.coprime_primes (prime_of_mem_Uset hu) (prime_of_mem_Vset hv)).2 (v_lt_u hL hu hv).ne')
  obtain ⟨n, hn⟩ := hcop.mul_dvd h2 h1
  refine ⟨n, ?_⟩
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (prime_of_mem_Uset hu).pos
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (prime_of_mem_Vset hv).pos
  have hCR : ((crt τ y u ξ z : ℕ) : ℝ) = (J : ℝ) + (u : ℝ) * v * n := by
    have := congrArg (fun m : ℤ => (m : ℝ)) hn
    push_cast at this
    rw [hC] at this
    push_cast at this
    linarith
  unfold phase
  rw [hCR]
  field_simp

/-- Uniqueness of `M` for coherent row labels. -/
lemma coherent_unique (hL : Large τ y) {ξ M M' : ℤ} (hM : |M| ≤ (y : ℤ) ^ 7)
    (hM' : |M'| ≤ (y : ℤ) ^ 7) (h1 : ∀ v ∈ Vset τ y, (v : ℤ) ∣ ξ - M)
    (h2 : ∀ v ∈ Vset τ y, (v : ℤ) ∣ ξ - M') : M = M' := by
  have hd : ((PV τ y : ℕ) : ℤ) ∣ M' - M := by
    apply prod_primes_dvd_int _ (fun v hv => prime_of_mem_Vset hv)
    intro v hv
    have := dvd_sub (h1 v hv) (h2 v hv)
    have e : ξ - M - (ξ - M') = M' - M := by ring
    rwa [e] at this
  have hlt : |M' - M| < (PV τ y : ℤ) := by
    have := PV_gt (τ := τ) hL
    have h3 := abs_sub M' M
    linarith
  have := Int.eq_zero_of_abs_lt_dvd hd hlt
  linarith

/-- Injectivity of the label map on frequencies (half of the CRT bijection): two frequencies
with the same residue modulo `P_V` and modulo every `u ∈ U` are equal. -/
lemma label_inj {h h' : ℤ} (hh : h ∈ freq (Lnum τ y Y))
    (hh' : h' ∈ freq (Lnum τ y Y)) (hV : (PV τ y : ℤ) ∣ h - h')
    (hU : ∀ u ∈ Uset y Y, (u : ℤ) ∣ h - h') : h = h' := by
  have hd : ((Lnum τ y Y : ℕ) : ℤ) ∣ h - h' := by
    apply prod_primes_dvd_int
    · intro p hp
      rcases Finset.mem_union.1 hp with h | h
      · exact prime_of_mem_Vset h
      · exact prime_of_mem_Uset h
    · intro p hp
      rcases Finset.mem_union.1 hp with hpV | hpU
      · have hvP : (p : ℤ) ∣ (PV τ y : ℤ) := by
          exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hpV
        exact hvP.trans hV
      · exact hU p hpU
  have hlt : |h - h'| < (Lnum τ y Y : ℤ) := by
    simp only [freq, Finset.mem_Ioc] at hh hh'
    rw [abs_lt]
    constructor <;> linarith
  have := Int.eq_zero_of_abs_lt_dvd hd hlt
  linarith

/-- Every frequency falls into exactly one of the three cases. -/
lemma three_cases (hL : Large τ y) (h : ℤ) :
    (CaseI τ y Y h ∨ CaseII τ y Y h ∨ CaseIII τ y h) ∧
    ¬ (CaseI τ y Y h ∧ CaseII τ y Y h) ∧ ¬ (CaseI τ y Y h ∧ CaseIII τ y h) ∧
    ¬ (CaseII τ y Y h ∧ CaseIII τ y h) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hc : Coherent τ y h
    · obtain ⟨M, hM, hMv⟩ := hc
      by_cases hU : ∀ u ∈ Uset y Y, (u : ℤ) ∣ h - M
      · exact Or.inl ⟨M, hM, hMv, hU⟩
      · push_neg at hU
        exact Or.inr (Or.inl ⟨M, hM, hMv, hU⟩)
    · exact Or.inr (Or.inr hc)
  · rintro ⟨⟨M, hM, hMv, hMu⟩, ⟨M', hM', hM'v, u, hu, hnd⟩⟩
    have := coherent_unique hL hM hM' hMv hM'v
    subst this
    exact hnd (hMu u hu)
  · rintro ⟨⟨M, hM, hMv, -⟩, hIII⟩
    exact hIII ⟨M, hM, hMv⟩
  · rintro ⟨⟨M, hM, hMv, -⟩, hIII⟩
    exact hIII ⟨M, hM, hMv⟩

/-- Every `|M| ≤ y^7` is a frequency. -/
lemma mem_freq_of_small (hL : Large τ y) {M : ℤ} (hM : |M| ≤ (y : ℤ) ^ 7) :
    M ∈ freq (Lnum τ y Y) := by
  have h := L_gt (Y := Y) hL
  simp only [freq, Finset.mem_Ioc]
  rw [abs_le] at hM
  constructor <;> omega

/-- Case I consists exactly of the frequencies `h` with `|h| ≤ y^7` (the major arcs). -/
lemma caseI_iff (hL : Large τ y) {h : ℤ} (hh : h ∈ freq (Lnum τ y Y)) :
    CaseI τ y Y h ↔ |h| ≤ (y : ℤ) ^ 7 := by
  constructor
  · rintro ⟨M, hM, hMv, hMu⟩
    have hPV : (PV τ y : ℤ) ∣ h - M := by
      apply prod_primes_dvd_int _ (fun v hv => prime_of_mem_Vset hv)
      exact hMv
    have := label_inj hh (mem_freq_of_small hL hM) hPV hMu
    rw [this]; exact hM
  · intro hsmall
    exact ⟨h, hsmall, fun v _ => by simp, fun u _ => by simp⟩

/-- `|φ(h)|` is the product of the column weights: `|φ(h)| = ∏_{u ∈ U} F_u(ξ, ζ_u)` with
`ξ = h mod P_V`, `ζ_u = h mod u`. -/
lemma norm_phi_eq_prod_Fcol (hL : Large τ y) (h : ℤ) :
    ‖phi (Aset τ y Y) h‖ =
      ∏ u ∈ Uset y Y, Fcol τ y u (h % (PV τ y : ℤ)).toNat (h % (u : ℤ)).toNat := by
  rw [norm_phi, Aset, Finset.prod_product_right]
  refine Finset.prod_congr rfl (fun u hu => ?_)
  unfold Fcol
  refine Finset.prod_congr rfl (fun v hv => ?_)
  have hPV0 : (PV τ y : ℤ) ≠ 0 := by
    have := PV_gt (τ := τ) hL
    have : (0 : ℤ) ≤ (y : ℤ) ^ 7 := by positivity
    omega
  have hu0 : (u : ℤ) ≠ 0 := by exact_mod_cast (prime_of_mem_Uset hu).ne_zero
  have hvP : (v : ℤ) ∣ (PV τ y : ℤ) := by
    exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hv
  have hJv : (v : ℤ) ∣ h - (((h % (PV τ y : ℤ)).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hPV0)]
    exact hvP.trans (Int.dvd_self_sub_emod)
  have hJu : (u : ℤ) ∣ h - (((h % (u : ℤ)).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hu0)]
    exact Int.dvd_self_sub_emod
  obtain ⟨n, hn⟩ := phase_congr hL hu hv _ _ h hJv hJu
  rw [hn, mul_add, mul_comm π ((n : ℤ) : ℝ), Real.cos_add_int_mul_pi, abs_mul, abs_neg_one_zpow,
    one_mul, mul_comm (u : ℝ)]

/-- eq. (4) Once the row labels `ξ` are fixed, the sum over column labels factorises:
`∑_ζ ∏_u F_u(ξ, ζ_u) = ∏_u S_u(ξ)`. -/
lemma eq_factor (ξ : ℕ) :
    ∑ ζ ∈ Fintype.piFinset (fun u : Uset y Y => range (u : ℕ)),
        ∏ u : Uset y Y, Fcol τ y u ξ (ζ u) =
      ∏ u ∈ Uset y Y, Scol τ y u ξ := by
  rw [← Finset.prod_coe_sort (Uset y Y) (fun u => Scol τ y u ξ)]
  unfold Scol
  exact (Finset.prod_univ_sum (fun u : Uset y Y => range (u : ℕ))
    (fun u z => Fcol τ y u ξ z)).symm

/-- Column weights are nonnegative. -/
lemma Fcol_nonneg (u ξ z : ℕ) : 0 ≤ Fcol τ y u ξ z :=
  Finset.prod_nonneg (fun _ _ => abs_nonneg _)

/-- Column weights are at most `1` (§6). -/
lemma Fcol_le_one (u ξ z : ℕ) : Fcol τ y u ξ z ≤ 1 :=
  Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => Real.abs_cos_le_one _)

/-- `S_u(ξ) ≥ 0`. -/
lemma Scol_nonneg (u ξ : ℕ) : 0 ≤ Scol τ y u ξ :=
  Finset.sum_nonneg (fun _ _ => Fcol_nonneg _ _ _)

end Erdos306
