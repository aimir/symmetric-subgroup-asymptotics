import SymmetricSubgroupAsymptotics.SubnormalCompositionRefinement
import Mathlib.GroupTheory.Index
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Every actual composition chain has length at most log₂ of the
actual group order. Proper subgroup inclusions double cardinality;
normality and simplicity are not extra hypotheses of that count. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCompositionLengthCardinality
variable {G : Type} [Group G] [Finite G]

theorem two_mul_card_le_of_lt {H K : Subgroup G} (h : H < K) :
    2 * Nat.card H ≤ Nat.card K := by
  have hlt : Nat.card H < Nat.card K := by
    apply lt_of_not_ge
    intro hc
    exact h.ne (Subgroup.eq_of_le_of_card_ge h.le hc)
  obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le h.le
  have hp := Nat.card_pos (α := H)
  have hd2 : 2 ≤ d := by nlinarith
  nlinarith

theorem two_pow_length_le_card (s : SubnormalCompositionSeries G) :
    2 ^ s.chain.length ≤ Nat.card G := by
  have hbound (j : Fin (s.chain.length + 1)) :
      2 ^ j.val ≤ Nat.card (s.chain j).val := by
    induction j using Fin.induction with
    | zero =>
      simpa only [Fin.val_zero, pow_zero] using Nat.card_pos (α := (s.chain 0).val)
    | succ j ih =>
      have hs : (s.chain j.castSucc).val < (s.chain j.succ).val := (s.chain.step j).1
      have hc := two_mul_card_le_of_lt hs
      simpa only [Fin.val_succ, pow_succ, Nat.mul_comm] using
        (Nat.mul_le_mul_left 2 ih).trans hc
  have h := hbound (Fin.last s.chain.length)
  change 2 ^ s.chain.length ≤ Nat.card s.chain.last.val at h
  simpa only [s.last, Subgroup.card_top] using h

theorem length_le_logb_card (s : SubnormalCompositionSeries G) :
    (s.chain.length : ℝ) ≤ Real.logb 2 (Nat.card G) := by
  have h := two_pow_length_le_card s
  have hr : (2 : ℝ) ^ s.chain.length ≤ (Nat.card G : ℝ) := by exact_mod_cast h
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ s.chain.length) hr
  simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using hh

end SymmetricSubgroupAsymptotics.CFSGCompositionLengthCardinality
