import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow15OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow15AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-! Complete literal row15 package from the six-configuration deleted-module
affine normal chain and the retained natural-module orbit witness. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRow15FinitePackage

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

noncomputable def finiteData :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoPrimitiveSixteenInterfaces.row15 :=
  .ofCertificates PrimitiveAffineDegreeTwoPrimitiveSixteenRow15AffineSocles.family
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow15OrbitWitness.natural

noncomputable def catalogueFiniteData :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.primitive16 (14 : Fin 20)) :=
  finiteData

noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization DegreeTwoPrimitiveSixteenInterfaces.row15 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoPrimitiveSixteenInterfaces.row15
      degreeTwoSixteenPairProfiles p :=
  finiteData.resolvedRow hZmud lit R

end PrimitiveAffineDegreeTwoPrimitiveSixteenRow15FinitePackage
end SymmetricSubgroupAsymptotics

end
