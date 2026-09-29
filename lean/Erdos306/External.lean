/-
External facts that the paper *cites* rather than proves.

This is the only file allowed to contain `sorry`.  Every statement here is a classical,
published result, transcribed as literally as possible.

* `ramanujan_theta` — Ramanujan (1919), *A proof of Bertrand's postulate*:
  `θ(x) - θ(x/2) > x/6 - 3√x` for `x > 300`, where `θ(x) = ∑_{p ≤ x} log p`
  (Mathlib's `Chebyshev.theta`).

Erdős' bound `∏_{p ≤ x} p ≤ 4^x`, the other input of Lemma 2.1, is in Mathlib
(`primorial_le_4_pow`) and is *not* assumed here.
-/
import Erdos306.Basic

namespace Erdos306

open Real

/-- The statement of **Ramanujan's inequality** [Ram19]: for every real `x > 300`,
`θ(x) - θ(x/2) > x/6 - 3√x`.  The whole development is proved (sorry-free) *assuming* this
statement (see `erdos_306_of_ramanujan` in `Main.lean`); the only `sorry` is its proof below. -/
def RamanujanInequality : Prop :=
  ∀ x : ℝ, 300 < x → x / 6 - 3 * Real.sqrt x < Chebyshev.theta x - Chebyshev.theta (x / 2)

/-- **Ramanujan's inequality** (cited in the proof of Lemma 2.1 of the paper, [Ram19]):
for every real `x > 300`, `θ(x) - θ(x/2) > x/6 - 3√x`.  External fact, not proved here. -/
theorem ramanujan_theta : RamanujanInequality := by
  sorry

end Erdos306
