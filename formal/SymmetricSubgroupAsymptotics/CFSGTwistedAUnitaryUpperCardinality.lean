import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperProductCard
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperCardBases
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralRadical
import Mathlib.Algebra.BigOperators.Intervals

/-! The exact order q^(r(r+1)/2) of the literal defining-fixed upper
subgroup. Each step counts the actual central kernel, vector quotient,
and smaller upper factor on the same matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists CFSGTwistedANaturalMatrices

theorem fixedRadical_card (q : CFSG.PrimePower) (s : ℕ) :
    Nat.card (fixedRadical q s) = q.order ^ (2 * s + 3) := by
  let f := fixedRadicalParameterHom q s
  have hc : Nat.card (fixedRadical q s) =
      Nat.card f.ker * Nat.card (Multiplicative (Fin (s + 1) → q.Extension 2)) := by
    rw [← f.ker.card_mul_index, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr (fixedRadicalParameterHom_surjective q s)]
    simp
  rw [hc, fixedRadicalParameterHom_kernel_card]
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, extension_two_card]
  rw [← pow_mul, ← pow_succ']
  congr 1

theorem naturalUnipotent_card_sum (q : CFSG.PrimePower) (r : ℕ) :
    Nat.card (naturalUnipotent r q) = q.order ^ (∑ i ∈ Finset.range (r + 1), i) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simpa using naturalUnipotent_card_zero q
    | succ r =>
      cases r with
      | zero => simpa [Finset.sum_range_succ] using naturalUnipotent_card_one q
      | succ s =>
        change Nat.card (naturalUnipotent (s + 2) q) = _
        rw [naturalUnipotent_card_step, fixedRadical_card, ih s (by omega), ← pow_add]
        congr 1
        conv_rhs => rw [Finset.sum_range_succ, Finset.sum_range_succ]
        omega

theorem naturalUnipotent_card (q : CFSG.PrimePower) (r : ℕ) :
    Nat.card (naturalUnipotent r q) = q.order ^ (r * (r + 1) / 2) := by
  rw [naturalUnipotent_card_sum, Finset.sum_range_id]
  simp only [Nat.add_sub_cancel, Nat.mul_comm]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
