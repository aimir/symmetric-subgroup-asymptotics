import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow7OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow7AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-! Complete literal row7 package from the product-complement
affine normal-generator bound and the retained natural-module orbit witness. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRow7FinitePackage

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

noncomputable def finiteData :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoPrimitiveSixteenInterfaces.row7 :=
  .ofCertificates PrimitiveAffineDegreeTwoPrimitiveSixteenRow7AffineSocles.family
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow7OrbitWitness.natural

noncomputable def catalogueFiniteData :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.primitive16 (6 : Fin 20)) :=
  finiteData

noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization DegreeTwoPrimitiveSixteenInterfaces.row7 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoPrimitiveSixteenInterfaces.row7
      degreeTwoSixteenPairProfiles p :=
  finiteData.resolvedRow hZmud lit R

end PrimitiveAffineDegreeTwoPrimitiveSixteenRow7FinitePackage
end SymmetricSubgroupAsymptotics

end
