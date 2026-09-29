/-
The statement of Erdős Problem #306 as formalised in Google DeepMind's `formal-conjectures`
repository (`FormalConjectures/ErdosProblems/306.lean`, theorem `Erdos306.erdos_306`), derived
from `Erdos306.erdos_306`.  There the statement reads `answer(sorry) ↔ P`; the theorem below
proves `P`, so the answer is `True`.
-/
import Erdos306.Main

namespace Erdos306

open ArithmeticFunction
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

/-- **Erdős Problem #306**, in the exact form of `formal-conjectures`: every positive rational
with squarefree denominator is `1/n_1 + ⋯ + 1/n_k` with `1 < n_1 < ⋯ < n_k`, each `n_i` a
product of two distinct primes (`ω(n_i) = Ω(n_i) = 2`). -/
theorem erdos_306_formal_conjectures : ∀ (q : ℚ), 0 < q → Squarefree q.den →
    ∃ k : ℕ, ∃ (n : Fin (k + 1) → ℕ), n 0 = 1 ∧ StrictMono n ∧
    (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 2 ∧ Ω (n i) = 2) ∧
    q = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) := by
  intro q hq hsq
  obtain ⟨F, hF, hsum⟩ := erdos_306 q hq hsq
  -- `F` is nonempty since `q > 0`
  obtain ⟨m, hm⟩ : ∃ m, F.card = m + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h => ?_
    rw [Finset.card_eq_zero.1 h, Finset.sum_empty] at hsum
    exact hq.ne' hsum.symm
  set e := F.orderEmbOfFin hm with he
  have heF : ∀ j, e j ∈ F := fun j => F.orderEmbOfFin_mem hm j
  have he2 : ∀ j, 1 < e j := by
    intro j
    obtain ⟨p, r, hp, hr, -, hpr⟩ := hF _ (heF j)
    rw [hpr]; exact one_lt_mul_of_lt_of_le hp.one_lt hr.one_lt.le
  -- the index set `{1, …, k}` is the image of `Fin.succ`
  have hIcc : Finset.Icc (1 : Fin (m + 2)) (Fin.last (m + 1)) =
      Finset.univ.map (Fin.succEmb (m + 1)) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_univ, true_and, Fin.coe_succEmb,
      Fin.exists_succ_eq, Fin.le_last, and_true]
    rw [Fin.le_iff_val_le_val, Fin.val_one, Ne, Fin.ext_iff, Fin.val_zero]
    omega
  refine ⟨m + 1, Fin.cons 1 (fun j => e j), rfl, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    induction i using Fin.cases with
    | zero => simp [he2 0]
    | succ j =>
      rw [← Fin.succ_castSucc]
      simp only [Fin.cons_succ]
      exact e.strictMono j.castSucc_lt_succ
  · rw [hIcc]
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hi
    obtain ⟨p, r, hp, hr, hpr, h⟩ := hF _ (heF j)
    simp only [Fin.coe_succEmb, Fin.cons_succ, h]
    refine ⟨?_, ?_⟩
    · rw [cardDistinctFactors_mul ((Nat.coprime_primes hp hr).2 hpr),
        cardDistinctFactors_apply_prime hp, cardDistinctFactors_apply_prime hr]
    · rw [cardFactors_mul hp.ne_zero hr.ne_zero, cardFactors_apply_prime hp,
        cardFactors_apply_prime hr]
  · have hmapF : Finset.univ.map e.toEmbedding = F := by
      ext x
      simp only [Finset.mem_map, Finset.mem_univ, true_and]
      exact Set.ext_iff.1 (F.range_orderEmbOfFin hm) x
    rw [hIcc, Finset.sum_map, ← hsum, ← hmapF, Finset.sum_map]
    simp

#print axioms Erdos306.erdos_306_formal_conjectures
