import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoFlagOrder
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoTorusKernel

/-! The actual original rank-two quotient has order at least
q^6(q^2-1)/3.  This counts its literal upper, opposite and unit-torus
images; no published order formula or named SU recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedA2DiagonalTorus CFSGSerreOrdinaryTwists

theorem rankTwoNaturalTorus_mem_flag (q : CFSG.PrimePower) (z : (q.Extension 2)ˣ) :
    rankTwoNaturalTorus q z ∈ rankTwoUpperFlag q := by
  apply (rankTwoUpperFlag_mem_iff q _).mpr
  rw [rankTwoNaturalTorus_matrix]
  intro i j hij
  exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)

theorem rankTwoProjectiveTorus_le_flag (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    (rankTwoProjectiveTorus q hq).range ≤
      (rankTwoUpperFlag q).map (rankTwoProjectiveCover q hq) := by
  rintro _ ⟨z, rfl⟩
  exact ⟨rankTwoNaturalTorus q z, rankTwoNaturalTorus_mem_flag q z, rfl⟩

theorem rankTwoProjectiveFlag_card_lower (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    q.order ^ 3 * Nat.card (rankTwoProjectiveTorus q hq).range ≤
      Nat.card ((rankTwoUpperFlag q).map (rankTwoProjectiveCover q hq)) := by
  letI : Finite (CFSG.Models.TwistedA 2 q) :=
    Finite.of_surjective (rankTwoProjectiveCover q hq) (rankTwoProjectiveCover_surjective q hq)
  let P := (rankTwoUpperSubgroup q).map (rankTwoProjectiveCover q hq)
  let T := (rankTwoProjectiveTorus q hq).range
  let B := (rankTwoUpperFlag q).map (rankTwoProjectiveCover q hq)
  have hd : Nat.card T ∣ q.order ^ 2 - 1 := by
    have hh := Subgroup.card_range_dvd (rankTwoProjectiveTorus q hq)
    rwa [Nat.card_units, CFSGTwistedANaturalMatrices.extension_two_card] at hh
  have hc2 : Nat.Coprime (q.order ^ 2) (q.order ^ 2 - 1) :=
    (Nat.coprime_self_sub_right (show 1 ≤ q.order ^ 2 by nlinarith)).mpr
      (Nat.coprime_one_right _)
  have hc : Nat.Coprime q.order (q.order ^ 2 - 1) :=
    Nat.Coprime.of_dvd_left (dvd_pow_self q.order (by decide : 2 ≠ 0)) hc2
  have hcop : Nat.Coprime (Nat.card P) (Nat.card T) := by
    change Nat.Coprime (Nat.card ((rankTwoUpperSubgroup q).map (rankTwoProjectiveCover q hq))) _
    rw [rankTwoProjectiveUpper_card]
    exact (hc.pow_left 3).coprime_dvd_right hd
  have hh := CFSGSubgroupProductInside.card_mul_le B P T
    (Subgroup.map_mono (rankTwoUpperSubgroup_le_flag q))
    (rankTwoProjectiveTorus_le_flag q hq) (Subgroup.inf_eq_bot_of_coprime hcop)
  change Nat.card ((rankTwoUpperSubgroup q).map (rankTwoProjectiveCover q hq)) * _ ≤ _ at hh
  rwa [rankTwoProjectiveUpper_card] at hh

theorem twistedA_rank_two_order_lower (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    q.order ^ 6 * (q.order ^ 2 - 1) ≤ 3 * Nat.card (CFSG.Models.TwistedA 2 q) := by
  have hT : q.order ^ 6 * Nat.card (rankTwoProjectiveTorus q hq).range ≤
      Nat.card (CFSG.Models.TwistedA 2 q) := by
    calc
      _ = q.order ^ 3 * (q.order ^ 3 * Nat.card (rankTwoProjectiveTorus q hq).range) := by ring
      _ ≤ q.order ^ 3 * Nat.card ((rankTwoUpperFlag q).map (rankTwoProjectiveCover q hq)) :=
        Nat.mul_le_mul_left _ (rankTwoProjectiveFlag_card_lower q hq)
      _ ≤ _ := rankTwoProjectiveFlag_order_bound q hq
  calc
    _ ≤ q.order ^ 6 * (3 * Nat.card (rankTwoProjectiveTorus q hq).range) :=
      Nat.mul_le_mul_left _ (rankTwoProjectiveTorus_card_lower q hq)
    _ = 3 * (q.order ^ 6 * Nat.card (rankTwoProjectiveTorus q hq).range) := by ring
    _ ≤ _ := Nat.mul_le_mul_left 3 hT

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
