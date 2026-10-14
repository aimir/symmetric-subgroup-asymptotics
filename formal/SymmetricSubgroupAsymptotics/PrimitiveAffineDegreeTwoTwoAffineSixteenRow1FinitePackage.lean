import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow1QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow1OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-! Complete finite data for the original two-affine row1. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow1FinitePackage

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

noncomputable def finiteData :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoTwoAffineSixteenInterfaces.row1 :=
  .ofCertificates PrimitiveAffineDegreeTwoTwoAffineSixteenRow1QuotientSocles.family
    PrimitiveAffineDegreeTwoTwoAffineSixteenRow1OrbitWitness.natural

noncomputable def catalogueFiniteData :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.twoAffine16 (0 : Fin 15)) :=
  finiteData

noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization DegreeTwoTwoAffineSixteenInterfaces.row1 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoTwoAffineSixteenInterfaces.row1
      degreeTwoSixteenPairProfiles p :=
  finiteData.resolvedRow hZmud lit R

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow1FinitePackage
end SymmetricSubgroupAsymptotics

end
