/-
§7 of the paper: Case I, the major arcs (Proposition 7.1), by positivity.
-/
import Erdos306.Table

namespace Erdos306

open Real Finset

variable (τ : ℚ) (y Y : ℕ)

/-- `P(M) = ∏_{(v,u) ∈ A} cos(π M/(uv))`. -/
noncomputable def Pmaj (M : ℤ) : ℝ :=
  ∏ p ∈ Aset τ y Y, Real.cos (π * ((M : ℝ) / ((p.1 : ℝ) * p.2)))

/-- `Σ_maj = (1/L) ∑_{|M| ≤ y^7} e(-Mτ) φ(M)`: the part of eq. (2) coming from case I. -/
noncomputable def SigmaMaj : ℂ :=
  (1 / (Lnum τ y Y : ℂ)) *
    ∑ M ∈ Finset.Icc (-(y : ℤ) ^ 7) ((y : ℤ) ^ 7), ee (-((M : ℝ) * τ)) * phi (Aset τ y Y) M

variable {τ y Y}

/-- `Re e(x) = cos 2πx`. -/
lemma ee_re (x : ℝ) : (ee x).re = Real.cos (2 * π * x) := by
  unfold ee
  rw [Complex.exp_re]
  have h1 : (2 * (π : ℂ) * Complex.I * x).re = 0 := by simp
  have h2 : (2 * (π : ℂ) * Complex.I * x).im = 2 * π * x := by simp
  rw [h1, h2, Real.exp_zero, one_mul]

/-- `Im e(x) = sin 2πx`. -/
lemma ee_im (x : ℝ) : (ee x).im = Real.sin (2 * π * x) := by
  unfold ee
  rw [Complex.exp_im]
  have h1 : (2 * (π : ℂ) * Complex.I * x).re = 0 := by simp
  have h2 : (2 * (π : ℂ) * Complex.I * x).im = 2 * π * x := by simp
  rw [h1, h2, Real.exp_zero, one_mul]

/-- Proposition 7.1, Step 1: `φ(M) = e(Mμ) P(M)`, hence `e(-Mτ) φ(M) = e(Mβ) P(M)` with
`β = μ - τ`. -/
lemma major_step1 (M : ℤ) :
    ee (-((M : ℝ) * τ)) * phi (Aset τ y Y) M =
      ee ((M : ℝ) * (mu τ y Y - τ)) * (Pmaj τ y Y M : ℂ) := by
  have hphi : phi (Aset τ y Y) M = ee ((M : ℝ) * mu τ y Y) * (Pmaj τ y Y M : ℂ) := by
    unfold phi Pmaj
    have : ∀ p ∈ Aset τ y Y, (1 + ee ((M : ℝ) / ((p.1 : ℝ) * p.2))) / 2 =
        ee ((M : ℝ) / ((p.1 : ℝ) * p.2) / 2) *
          (Real.cos (π * ((M : ℝ) / ((p.1 : ℝ) * p.2))) : ℂ) := by
      intro p _
      rw [eq_half]; ring
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, ← ee_sum, Complex.ofReal_prod]
    congr 2
    unfold mu
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    ring
  rw [hphi, ← mul_assoc, ← ee_add]
  congr 2
  ring

/-- Proposition 7.1, Step 2: `P(M) > 0` for `|M| ≤ y^7`; `P(0) = 1`; `P(-M) = P(M)`. -/
lemma major_step2 (hL : Large τ y) {M : ℤ} (hM : |M| ≤ (y : ℤ) ^ 7) :
    0 < Pmaj τ y Y M := by
  unfold Pmaj
  refine Finset.prod_pos (fun p hp => ?_)
  obtain ⟨hv, hu⟩ := mem_Aset.1 hp
  have hv2 := (le_of_mem_Vset hL hv).1
  have hu8 := (bounds_of_mem_Uset hu).1
  have hy := hL.y_ge
  -- `2|M| ≤ 2y^7 < 2y^8 < vu`
  have hy78 : y ^ 7 < y ^ 8 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hMR : |(M : ℝ)| ≤ (y : ℝ) ^ 7 := by exact_mod_cast hM
  have hprod : 2 * (y : ℝ) ^ 8 < (p.1 : ℝ) * p.2 := by
    have : 2 * y ^ 8 < p.1 * p.2 := by nlinarith
    exact_mod_cast this
  have hy78R : (y : ℝ) ^ 7 < (y : ℝ) ^ 8 := by exact_mod_cast hy78
  have hpos : (0 : ℝ) < (p.1 : ℝ) * p.2 := by
    have : (0 : ℝ) ≤ (y : ℝ) ^ 8 := by positivity
    linarith
  have hx : |(M : ℝ) / ((p.1 : ℝ) * p.2)| < 1 / 2 := by
    rw [abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
    linarith
  apply Real.cos_pos_of_mem_Ioo
  rw [abs_lt] at hx
  constructor <;> nlinarith [Real.pi_pos]

/-- Proposition 7.1, Step 2: `P(0) = 1`. -/
lemma Pmaj_zero : Pmaj τ y Y 0 = 1 := by
  simp [Pmaj]

/-- Proposition 7.1, Step 2: `P(-M) = P(M)` (cosine is even). -/
lemma Pmaj_neg (M : ℤ) : Pmaj τ y Y (-M) = Pmaj τ y Y M := by
  unfold Pmaj
  refine Finset.prod_congr rfl (fun p _ => ?_)
  push_cast
  rw [neg_div, mul_neg, Real.cos_neg]

/-- **Proposition 7.1 (major arcs).**  `Σ_maj` is real and `Σ_maj ≥ 1/L`.
(Pair `M` with `-M`: the contribution is `2 cos(2πMβ) P(M) ≥ 0`, since `|2πMβ| < π/2` by the
tuning lemma; and `M = 0` contributes `1/L`.) -/
theorem prop_major (hL : Large τ y) (hT : Tuned τ y Y) :
    (SigmaMaj τ y Y).im = 0 ∧ 1 / (Lnum τ y Y : ℝ) ≤ (SigmaMaj τ y Y).re := by
  set β : ℝ := mu τ y Y - τ with hβ
  set K : ℤ := (y : ℤ) ^ 7 with hK
  have hS : SigmaMaj τ y Y = ((1 / (Lnum τ y Y : ℝ) : ℝ) : ℂ) *
      ∑ M ∈ Finset.Icc (-K) K, ee ((M : ℝ) * β) * (Pmaj τ y Y M : ℂ) := by
    unfold SigmaMaj
    rw [Finset.sum_congr rfl (fun M _ => major_step1 M)]
    push_cast; ring
  have hre : ∀ M : ℤ, (ee ((M : ℝ) * β) * (Pmaj τ y Y M : ℂ)).re =
      Real.cos (2 * π * ((M : ℝ) * β)) * Pmaj τ y Y M := by
    intro M; rw [Complex.mul_re, ee_re]; simp
  have him : ∀ M : ℤ, (ee ((M : ℝ) * β) * (Pmaj τ y Y M : ℂ)).im =
      Real.sin (2 * π * ((M : ℝ) * β)) * Pmaj τ y Y M := by
    intro M; rw [Complex.mul_im, ee_im]; simp
  have hLpos : (0 : ℝ) < 1 / (Lnum τ y Y : ℝ) := by
    have h1 := L_gt (Y := Y) hL
    have h2 : (0 : ℤ) ≤ (y : ℤ) ^ 7 := by positivity
    have : (0 : ℤ) < (Lnum τ y Y : ℤ) := by linarith
    have : (0 : ℝ) < (Lnum τ y Y : ℝ) := by exact_mod_cast this
    positivity
  constructor
  · -- Step 3: pairing `M ↔ -M` makes the sum real
    rw [hS, Complex.im_ofReal_mul, Complex.im_sum]
    simp only [him]
    have : ∑ M ∈ Finset.Icc (-K) K, Real.sin (2 * π * ((M : ℝ) * β)) * Pmaj τ y Y M = 0 := by
      refine Finset.sum_involution (fun M _ => -M) ?_ ?_ ?_ ?_
      · intro M _
        rw [Pmaj_neg]; push_cast
        rw [show 2 * π * (-(M : ℝ) * β) = -(2 * π * ((M : ℝ) * β)) by ring, Real.sin_neg]
        ring
      · intro M _ hne heq
        apply hne
        change -M = M at heq
        have : M = 0 := by omega
        subst this; simp
      · intro M hM; simp only [Finset.mem_Icc] at hM ⊢; omega
      · intro M _; simp
    rw [this, mul_zero]
  · -- Step 4: every term is nonnegative, and `M = 0` contributes `1`
    rw [hS, Complex.re_ofReal_mul, Complex.re_sum]
    simp only [hre]
    have hβ1 : |β| ≤ HV τ y / (2 * (y : ℝ) ^ 8) := by
      rw [abs_le]
      constructor
      · linarith [hT.beta_ge]
      · have := hT.beta_nonpos
        have hHV := HV_pos hL
        have : 0 ≤ HV τ y / (2 * (y : ℝ) ^ 8) := by positivity
        linarith
    have hy : (3 : ℝ) ≤ y := by exact_mod_cast hL.y_ge
    have hterm : ∀ M ∈ Finset.Icc (-K) K,
        0 ≤ Real.cos (2 * π * ((M : ℝ) * β)) * Pmaj τ y Y M := by
      intro M hM
      have hMabs : |M| ≤ K := abs_le.2 (Finset.mem_Icc.1 hM)
      refine mul_nonneg ?_ (major_step2 hL hMabs).le
      apply Real.cos_nonneg_of_mem_Icc
      -- `|2 M β| ≤ 2 y^7 · H_V/(2y^8) = H_V / y < 1/2`
      have hMR : |(M : ℝ)| ≤ (y : ℝ) ^ 7 := by exact_mod_cast hMabs
      have hy0 : (0 : ℝ) < y := by linarith
      have hb : |(M : ℝ) * β| ≤ (y : ℝ) ^ 7 * (HV τ y / (2 * (y : ℝ) ^ 8)) := by
        rw [abs_mul]
        exact mul_le_mul hMR hβ1 (abs_nonneg _) (by positivity)
      have he : (y : ℝ) ^ 7 * (HV τ y / (2 * (y : ℝ) ^ 8)) = HV τ y / (2 * y) := by
        field_simp
      rw [he] at hb
      have hmaj := hL.major
      have : HV τ y / (2 * y) < 1 / 4 := by
        rw [div_lt_iff₀ (by positivity)]; linarith
      rw [abs_le] at hb
      constructor <;> nlinarith [Real.pi_pos]
    have h0mem : (0 : ℤ) ∈ Finset.Icc (-K) K := by
      simp only [Finset.mem_Icc]
      have : (0 : ℤ) ≤ K := by positivity
      omega
    have := Finset.single_le_sum hterm h0mem
    simp only [Int.cast_zero, zero_mul, mul_zero, Real.cos_zero, one_mul, Pmaj_zero] at this
    nlinarith

end Erdos306
