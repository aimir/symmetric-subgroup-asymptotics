import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow6OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow6AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-! Complete literal row6 package from the cyclic or metacyclic
affine normal-generator bound and the retained natural-module orbit witness. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRow6FinitePackage

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

noncomputable def finiteData :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoPrimitiveSixteenInterfaces.row6 :=
  .ofCertificates PrimitiveAffineDegreeTwoPrimitiveSixteenRow6AffineSocles.family
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow6OrbitWitness.natural

noncomputable def catalogueFiniteData :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.primitive16 (5 : Fin 20)) :=
  finiteData

noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization DegreeTwoPrimitiveSixteenInterfaces.row6 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoPrimitiveSixteenInterfaces.row6
      degreeTwoSixteenPairProfiles p :=
  finiteData.resolvedRow hZmud lit R

end PrimitiveAffineDegreeTwoPrimitiveSixteenRow6FinitePackage
end SymmetricSubgroupAsymptotics

end
