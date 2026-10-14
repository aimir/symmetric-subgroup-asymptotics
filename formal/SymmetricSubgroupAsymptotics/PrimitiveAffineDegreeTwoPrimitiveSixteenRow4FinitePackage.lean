import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow4OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow4AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-! Complete literal row4 package from the product-complement
affine normal-generator bound and the retained natural-module orbit witness. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRow4FinitePackage

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

noncomputable def finiteData :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoPrimitiveSixteenInterfaces.row4 :=
  .ofCertificates PrimitiveAffineDegreeTwoPrimitiveSixteenRow4AffineSocles.family
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow4OrbitWitness.natural

noncomputable def catalogueFiniteData :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.primitive16 (3 : Fin 20)) :=
  finiteData

noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization DegreeTwoPrimitiveSixteenInterfaces.row4 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoPrimitiveSixteenInterfaces.row4
      degreeTwoSixteenPairProfiles p :=
  finiteData.resolvedRow hZmud lit R

end PrimitiveAffineDegreeTwoPrimitiveSixteenRow4FinitePackage
end SymmetricSubgroupAsymptotics

end
