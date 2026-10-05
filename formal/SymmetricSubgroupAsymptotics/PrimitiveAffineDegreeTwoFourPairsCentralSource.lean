import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoCentralProductTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoCentralProductWidthEightNumerics
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairQuotientPackage

/-!
# The two central-product rows in the four-pair slice

The same abstract groups `A4 × C2` and `S4 × C2` occur at width eight.
Their normal-axis theorem is representation independent.  A literal group
equivalence supplied by the finite four-pair correspondence therefore pulls
the already checked datum back to the retained action, while the width-eight
module supplies the separate physical pointing and numerical margin.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private abbrev C2 := Multiplicative (ZMod 2)
private abbrev A4 := NaturalA4ScalarFourHead.G
private abbrev S4 := Equiv.Perm (Fin 4)

/-- The two literal abstract-group models.  This is correspondence data,
not a counting hypothesis. -/
inductive PublishedFourPairCentralModel
    (U : PreE7NonPairActionClass 8) : Type
  | alternatingFourTimesTwo
      (equiv : preE7NonPairAction 8 U ≃* A4 × C2)
  | symmetricFourTimesTwo
      (equiv : preE7NonPairAction 8 U ≃* S4 × C2)

namespace PublishedFourPairCentralModel

/-- Pull the representation-independent central-product theorem to the
literal width-eight action. -/
noncomputable def literalData
    {U : PreE7NonPairActionClass 8}
    (M : PublishedFourPairCentralModel U) :
    PreE7DegreeEightCentralProductSource.Data U :=
  match M with
  | .alternatingFourTimesTwo e =>
      CentralBinaryProductModels.a4TimesTwo.comapEquiv e
  | .symmetricFourTimesTwo e =>
      CentralBinaryProductModels.s4TimesTwo.comapEquiv e

/-- Raw pre-padding envelope, retained for degree-three composition. -/
noncomputable def quotientSummedEnvelope
    {U : PreE7NonPairActionClass 8}
    (M : PublishedFourPairCentralModel U) :
    PreE7DegreeTwoPairQuotientSummedEnvelope (preE7NonPairAction 8 U) :=
  M.literalData.quotientSummedEnvelope

/-- The same raw row with the faithful five-point action of its retained
quotient comparator. -/
noncomputable def quotientSummedPackage
    {U : PreE7NonPairActionClass 8}
    (M : PublishedFourPairCentralModel U) :
    PreE7DegreeTwoPairQuotientSummedPackage
      (preE7NonPairAction 8 U) where
  envelope := M.quotientSummedEnvelope
  v := 5
  action := M.literalData.action
  action_injective := M.literalData.action_injective

/-- Final width-eight source used by the affine residual dispatcher. -/
noncomputable def source
    {U : PreE7NonPairActionClass 8}
    (M : PublishedFourPairCentralModel U) :
    PreE7RankTailSourceOrYonedaTopData 8 U :=
  .inl (PreE7DegreeEightCentralProductSource.rankTailOwnerSource M.literalData)

end PublishedFourPairCentralModel
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
