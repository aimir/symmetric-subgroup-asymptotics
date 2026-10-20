import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow11OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRows9And11AugmentationSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-! Complete original zero16 row11: the structural augmentation
normal-cover route supplies every quotient-socle bound, and the checked
literal orbit witness supplies the natural module bound. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow11FinitePackage

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

noncomputable def finiteData :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoZeroSixteenInterfaces.row11 :=
  .ofCertificates
    PrimitiveAffineDegreeTwoZeroSixteenRows9And11AugmentationSocles.row11Socle
    PrimitiveAffineDegreeTwoZeroSixteenRow11OrbitWitness.natural

noncomputable def catalogueFiniteData :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.zero16 (10 : Fin 29)) :=
  finiteData

noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization DegreeTwoZeroSixteenInterfaces.row11 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoZeroSixteenInterfaces.row11
      degreeTwoSixteenPairProfiles p :=
  finiteData.resolvedRow hZmud lit R

end PrimitiveAffineDegreeTwoZeroSixteenRow11FinitePackage
end SymmetricSubgroupAsymptotics

end

