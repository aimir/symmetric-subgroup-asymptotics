import SymmetricSubgroupAsymptotics.PrimitiveTwelvePairActualSource
import SymmetricSubgroupAsymptotics.MarkedC4ActualNormalGeneratorDensity
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! A coarser finite-package adapter. Primitive degree12 has one simple
full-socle factor; every nonzero normal quotient has order at most ten.
Consequently three actual normal generators suffice for each quotient
socle. This does not assert that the normal lattice is a chain. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

variable {G : Type} [Group G] [Finite G] [MulAction G (Fin 12)]
    [FaithfulSMul G (Fin 12)]

omit [FaithfulSMul G (Fin 12)] in
theorem NonaffineData.degreeTwelve_quotientSocle_three
    (D : NonaffineData G (Fin 12)) (hindex : PublishedSimpleIndexBounds)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) 3 := by
  by_cases hN : N=⊥
  · subst N
    exact CyclicSocleQuotientTools.socleBound_equiv QuotientGroup.quotientBot.symm
      ((D.degreeTwelve_socle_one hindex).mono (by decide))
  · apply (socleNormalGeneratorBound_iff_normalGen_le (G ⧸ N) 3).mpr
    have hpow := MarkedC4.ActualNormalGeneratorDensity.two_pow_normalGen_le_card
      (finiteGroupSocle (G ⧸ N))
    have hs : Nat.card (finiteGroupSocle (G ⧸ N)) ≤ 10 :=
      (Nat.card_le_card_of_injective (Subtype.val : finiteGroupSocle (G ⧸ N) → G ⧸ N)
        Subtype.val_injective).trans
        (D.degreeTwelve_nonzero_normal_quotient_card_le_ten hindex N hN)
    by_contra h
    have hr : 4 ≤ MarkedC4.normalGen (finiteGroupSocle (G ⧸ N)) := by omega
    have hp : (16 : ℕ) ≤ 10 := calc
      16=2^4 := by decide
      _ ≤ 2^MarkedC4.normalGen (finiteGroupSocle (G ⧸ N)) :=
        pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hr
      _ ≤ Nat.card (finiteGroupSocle (G ⧸ N)) := hpow
      _ ≤ 10 := hs
    omega

/-- This parameter is the ordinary retained simple-index theorem only. -/
theorem primitive_degreeTwelve_quotientSocle_three
    [MulAction.IsPreprimitive G (Fin 12)]
    (hindex : PublishedSimpleIndexBounds) (N : Subgroup G) [N.Normal] :
    SocleNormalGeneratorBound (G ⧸ N) 3 :=
  (Classical.choice PrimitiveTwelvePairActualSource.nonaffine).degreeTwelve_quotientSocle_three
    hindex N

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
