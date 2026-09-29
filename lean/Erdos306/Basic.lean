/-
Erdős Problem #306 — formalisation of S. Li, "Unit fractions with semiprime denominators:
an elementary solution of Erdős Problem #306" (paper/erdos306.tex).

Basic notation shared by all files:
* `nint x`  — the distance `‖x‖` from a real number to the nearest integer (paper §8);
* `ee x`    — the additive character `e(x) = exp(2πix)` (paper §5).
-/
import Mathlib

open Real

namespace Erdos306

/-- `‖x‖`: the distance from the real number `x` to the nearest integer (paper, §8). -/
noncomputable def nint (x : ℝ) : ℝ := |x - round x|

/-- `e(x) = exp(2πix)` (paper, §5). -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

/-- `‖x‖ ≥ 0`. -/
lemma nint_nonneg (x : ℝ) : 0 ≤ nint x := abs_nonneg _

/-- `‖x‖ ≤ 1/2`. -/
lemma nint_le_half (x : ℝ) : nint x ≤ 1 / 2 := abs_sub_round x

/-- `‖x‖ ≤ |x - n|` for every integer `n`. -/
lemma nint_le_abs_sub (x : ℝ) (n : ℤ) : nint x ≤ |x - n| := round_le x n

/-- `‖x‖ ≤ |x|`. -/
lemma nint_le_abs (x : ℝ) : nint x ≤ |x| := by
  simpa using nint_le_abs_sub x 0

/-- `‖x + n‖ = ‖x‖` for integers `n`. -/
lemma nint_add_int (x : ℝ) (n : ℤ) : nint (x + n) = nint x := by
  unfold nint
  rw [round_add_intCast]
  push_cast
  congr 1
  ring

/-- `‖x - n‖ = ‖x‖` for integers `n`. -/
lemma nint_sub_int (x : ℝ) (n : ℤ) : nint (x - n) = nint x := by
  have := nint_add_int x (-n)
  simpa [sub_eq_add_neg] using this

/-- `‖-x‖ = ‖x‖`. -/
lemma nint_neg (x : ℝ) : nint (-x) = nint x := by
  apply le_antisymm
  · calc nint (-x) ≤ |-x - ((-round x : ℤ) : ℝ)| := nint_le_abs_sub _ _
      _ = nint x := by unfold nint; push_cast; rw [← abs_neg]; ring_nf
  · calc nint x ≤ |x - ((-round (-x) : ℤ) : ℝ)| := nint_le_abs_sub _ _
      _ = nint (-x) := by unfold nint; push_cast; rw [← abs_neg]; ring_nf

/-- Triangle inequality for `‖·‖`. -/
lemma nint_add_le (x z : ℝ) : nint (x + z) ≤ nint x + nint z := by
  calc nint (x + z) ≤ |x + z - ((round x + round z : ℤ) : ℝ)| := nint_le_abs_sub _ _
    _ = |(x - round x) + (z - round z)| := by push_cast; ring_nf
    _ ≤ nint x + nint z := abs_add_le _ _

/-- `‖x - z‖ ≤ ‖x‖ + ‖z‖`. -/
lemma nint_sub_le (x z : ℝ) : nint (x - z) ≤ nint x + nint z := by
  have := nint_add_le x (-z)
  rw [nint_neg] at this
  simpa [sub_eq_add_neg] using this

/-- If `‖x‖ ≤ d` then some integer `n` has `|x - n| ≤ d`. -/
lemma exists_int_of_nint_le {x d : ℝ} (h : nint x ≤ d) : ∃ n : ℤ, |x - n| ≤ d :=
  ⟨round x, h⟩

/-- `e(x + z) = e(x) e(z)`. -/
lemma ee_add (x z : ℝ) : ee (x + z) = ee x * ee z := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `e(0) = 1`. -/
lemma ee_zero : ee 0 = 1 := by simp [ee]

/-- `|e(x)| = 1`. -/
lemma norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [Complex.norm_exp]
  simp

end Erdos306
