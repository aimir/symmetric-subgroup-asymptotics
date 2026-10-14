import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow10QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow10OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-! Complete finite data for the original two-affine row10. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow10FinitePackage

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

noncomputable def finiteData :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoTwoAffineSixteenInterfaces.row10 :=
  .ofCertificates PrimitiveAffineDegreeTwoTwoAffineSixteenRow10QuotientSocles.family
    PrimitiveAffineDegreeTwoTwoAffineSixteenRow10OrbitWitness.natural

noncomputable def catalogueFiniteData :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.twoAffine16 (9 : Fin 15)) :=
  finiteData

noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization DegreeTwoTwoAffineSixteenInterfaces.row10 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoTwoAffineSixteenInterfaces.row10
      degreeTwoSixteenPairProfiles p :=
  finiteData.resolvedRow hZmud lit R

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow10FinitePackage
end SymmetricSubgroupAsymptotics

end
