import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow20OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow20AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-! Complete literal row20 package from the fifteen-heptad binary-module
affine normal chain and the retained natural-module orbit witness. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRow20FinitePackage

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

noncomputable def finiteData :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoPrimitiveSixteenInterfaces.row20 :=
  .ofCertificates PrimitiveAffineDegreeTwoPrimitiveSixteenRow20AffineSocles.family
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow20OrbitWitness.natural

noncomputable def catalogueFiniteData :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.primitive16 (19 : Fin 20)) :=
  finiteData

noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization DegreeTwoPrimitiveSixteenInterfaces.row20 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoPrimitiveSixteenInterfaces.row20
      degreeTwoSixteenPairProfiles p :=
  finiteData.resolvedRow hZmud lit R

end PrimitiveAffineDegreeTwoPrimitiveSixteenRow20FinitePackage
end SymmetricSubgroupAsymptotics

end
