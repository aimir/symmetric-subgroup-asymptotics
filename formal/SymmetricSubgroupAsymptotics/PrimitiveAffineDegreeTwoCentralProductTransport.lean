import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoCentralProductModels
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoCentralProductLiteralEnvelope

/-!
# Transport of the two literal central-product sources

The finite catalogue identifies the original six-point action with one of
the two abstract product models.  This file transports the checked normal
axis, quotient action, and every epimorphism estimate back to the literal
original action.  No count is repeated after transport.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

namespace PreE7CentralProductRankTailData

/-- Pull a literal central-product datum back through an actual group
equivalence.  The retained layer is the literal inverse image, and every
normal quotient is transported by `QuotientGroup.congr`. -/
noncomputable def comapEquiv
    {Q Q' : Type} [Group Q] [Finite Q] [Group Q'] [Finite Q']
    (e : Q ≃* Q') (D : PreE7CentralProductRankTailData Q') :
    PreE7CentralProductRankTailData Q where
  E := D.E.comap e.toMonoidHom
  action := D.action.comp
    (QuotientGroup.congr (D.E.comap e.toMonoidHom) D.E e
      (Subgroup.map_comap_eq_self_of_surjective
        (f := e.toMonoidHom) e.surjective D.E)).toMonoidHom
  action_injective := D.action_injective.comp
    (QuotientGroup.congr (D.E.comap e.toMonoidHom) D.E e
      (Subgroup.map_comap_eq_self_of_surjective
        (f := e.toMonoidHom) e.surjective D.E)).injective
  lowerConstant := D.lowerConstant
  lowerConstant_nonneg := D.lowerConstant_nonneg
  lower_axis_cold := by
    intro N b J hN hJ
    let M : Subgroup Q' := N.1.map e.toMonoidHom
    haveI hM : M.Normal := N.2.map e.toMonoidHom e.surjective
    have hnot : ¬ D.E ≤ M := by
      intro hle
      apply hN
      intro x hx
      have hex : e x ∈ M := hle hx
      rcases hex with ⟨y, hy, hey⟩
      have hxy : x = y := e.injective hey.symm
      simpa only [hxy] using hy
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J)
      (QuotientGroup.congr N.1 M e rfl)]
    exact D.lower_axis_cold ⟨M, hM⟩ b J hnot hJ
  order_le := by
    rw [Nat.card_congr e.toEquiv]
    exact D.order_le

end PreE7CentralProductRankTailData

private abbrev C2 := Multiplicative (ZMod 2)
private abbrev A4 := NaturalA4ScalarFourHead.G
private abbrev S4 := Equiv.Perm (Fin 4)

/-- The two exceptional three-pair abstract groups in the published
degree-six catalogue.  Only a literal group equivalence is retained here;
the counting datum is the theorem proved for the corresponding model. -/
inductive PublishedThreePairCentralModel
    (U : PreE7NonPairActionClass 6) : Type
  | alternatingFourTimesTwo
      (equiv : preE7NonPairAction 6 U ≃* A4 × C2)
  | symmetricFourTimesTwo
      (equiv : preE7NonPairAction 6 U ≃* S4 × C2)

namespace PublishedThreePairCentralModel

/-- Transport the checked literal normal-axis theorem to the selected
six-point original action. -/
noncomputable def literalData
    {U : PreE7NonPairActionClass 6}
    (M : PublishedThreePairCentralModel U) :
    PreE7CentralProductRankTailData (preE7NonPairAction 6 U) :=
  match M with
  | .alternatingFourTimesTwo e =>
      CentralBinaryProductModels.a4TimesTwo.comapEquiv e
  | .symmetricFourTimesTwo e =>
      CentralBinaryProductModels.s4TimesTwo.comapEquiv e

/-- The complete action-facing correlated source. -/
noncomputable def source
    {U : PreE7NonPairActionClass 6}
    (M : PublishedThreePairCentralModel U) :
    PreE7DegreeSixCentralProductSource U :=
  .ofLiteral M.literalData

/-- The raw literal quotient envelope used by the degree-three prepend. -/
noncomputable def quotientSummedEnvelope
    {U : PreE7NonPairActionClass 6}
    (M : PublishedThreePairCentralModel U) :
    PreE7DegreeTwoPairQuotientSummedEnvelope
      (preE7NonPairAction 6 U) :=
  M.literalData.quotientSummedEnvelope

end PublishedThreePairCentralModel

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
