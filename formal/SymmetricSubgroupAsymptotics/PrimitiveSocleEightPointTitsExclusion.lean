import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart
import SymmetricSubgroupAsymptotics.CFSGReeFFourAllParameterOrderLower
import Mathlib.Data.Finite.Perm

/-! The actual simple socle factor has order at most the original
faithful permutation group. The proved SAME original Tits order lower
bound excludes it on at most eight points, without a sporadic/order table
or a finite action classification. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleEightPointTitsExclusion
open PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem simple_card_le_group_card : Nat.card D.Simple ≤ Nat.card G := by
  have hpow : Nat.card D.Simple ≤ Nat.card D.Simple^D.factorCount := by
    simpa only [pow_one] using Nat.pow_le_pow_right (Nat.card_pos (α := D.Simple))
      (show 1 ≤ D.factorCount from D.factorCount_pos)
  have hs : Nat.card (finiteGroupSocle G) = Nat.card D.Simple^D.factorCount := by
    rw [Nat.card_congr D.socleEquiv.toEquiv,Nat.card_fun,Nat.card_fin]
  have hN := Nat.card_le_card_of_injective
    (finiteGroupSocle G).subtype (finiteGroupSocle G).subtype_injective
  exact (hpow.trans_eq hs.symm).trans hN

theorem simple_card_le_degree_factorial [FaithfulSMul G X] :
    Nat.card D.Simple ≤ (Nat.card X).factorial := by
  have hG := Nat.card_le_card_of_injective (MulAction.toPermHom G X) MulAction.toPerm_injective
  exact (simple_card_le_group_card D).trans (by simpa only [Nat.card_perm] using hG)

theorem not_tits_of_degree_le_eight [FaithfulSMul G X] (hsmall : Nat.card X ≤ 8)
    (e : D.Simple ≃* CFSG.Models.Tits) : False := by
  have hT := CFSGReeFFourAllParameterOrderLower.tits_order_lower
  have hcard := simple_card_le_degree_factorial D
  rw [Nat.card_congr e.toEquiv] at hcard
  have hfac : (Nat.card X).factorial ≤ 40320 := by
    simpa only [show Nat.factorial 8 = 40320 by decide] using Nat.factorial_le hsmall
  omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleEightPointTitsExclusion
