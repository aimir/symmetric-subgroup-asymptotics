import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow4QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow4OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-! Complete finite data for the original two-affine row4. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow4FinitePackage

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

noncomputable def finiteData :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoTwoAffineSixteenInterfaces.row4 :=
  .ofCertificates PrimitiveAffineDegreeTwoTwoAffineSixteenRow4QuotientSocles.family
    PrimitiveAffineDegreeTwoTwoAffineSixteenRow4OrbitWitness.natural

noncomputable def catalogueFiniteData :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.twoAffine16 (3 : Fin 15)) :=
  finiteData

noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization DegreeTwoTwoAffineSixteenInterfaces.row4 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoTwoAffineSixteenInterfaces.row4
      degreeTwoSixteenPairProfiles p :=
  finiteData.resolvedRow hZmud lit R

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow4FinitePackage
end SymmetricSubgroupAsymptotics

end
