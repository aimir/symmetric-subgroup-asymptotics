import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedWordOrder
import SymmetricSubgroupAsymptotics.PrimitiveSocleElementarySylowOrderFourExclusion

/-! A supported actual socle factor preserves the selected Co3 word's
order inside the original source. Its faithful original action cannot
have at most8points. This excludes Co3 from the SAME actual Top8 witness,
without removing it from unrelated global failed-half actions up to10. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleCoThreeDegreeEightExclusion
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X)

theorem not_co_three (hcard : Nat.card X ≤ 8)
    (e : D.Simple ≃* CFSG.Models.MatrixGroups.Co3.Model) : False := by
  have hn : ¬ IsMulCommutative CFSG.Models.MatrixGroups.Co3.Model := by
    intro hc
    apply D.noncommutative
    apply isMulCommutative_iff.mpr
    intro x y
    apply e.injective
    have h := (isMulCommutative_iff.mp hc) (e x) (e y)
    simpa only [map_mul] using h
  let i : Fin D.factorCount := ⟨0,D.factorCount_pos⟩
  let axis : D.Simple →* G := MinimalNormalIsotypicRelativeOrdinaryGenerators.axisHom
    (finiteGroupSocle G) D.socleEquiv i
  have haxis : Function.Injective axis := Subtype.coe_injective.comp
    (MinimalNormalIsotypicRelativeOrdinaryGenerators.axisMap_injective
      (finiteGroupSocle G) D.socleEquiv i)
  let f : CFSG.Models.MatrixGroups.Co3.Model →* Equiv.Perm X :=
    (MulAction.toPermHom G X).comp (axis.comp e.symm.toMonoidHom)
  have hf : Function.Injective f :=
    MulAction.toPerm_injective.comp (haxis.comp e.symm.injective)
  have h := CFSGCoThreeSelectedWordOrder.nine_le_card_of_faithful_permutation_action hn f hf
  omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleCoThreeDegreeEightExclusion
