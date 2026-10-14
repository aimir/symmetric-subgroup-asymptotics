import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow15QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow15OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-! Complete finite data for the original two-affine row15, using its exact
local affine wreath chart and the checked four-orbit natural module. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow15FinitePackage

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

noncomputable def finiteData :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoTwoAffineSixteenInterfaces.row15 :=
  .ofCertificates PrimitiveAffineDegreeTwoTwoAffineSixteenRow15QuotientSocles.family
    PrimitiveAffineDegreeTwoTwoAffineSixteenRow15OrbitWitness.natural

noncomputable def catalogueFiniteData :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.twoAffine16 (14 : Fin 15)) :=
  finiteData

noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization DegreeTwoTwoAffineSixteenInterfaces.row15 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoTwoAffineSixteenInterfaces.row15
      degreeTwoSixteenPairProfiles p :=
  finiteData.resolvedRow hZmud lit R

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow15FinitePackage
end SymmetricSubgroupAsymptotics

end
