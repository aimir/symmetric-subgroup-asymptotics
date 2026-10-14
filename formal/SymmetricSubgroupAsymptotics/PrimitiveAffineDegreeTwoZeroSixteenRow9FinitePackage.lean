import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow9OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRows9And11AugmentationSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-! Complete original zero16 row9: the structural augmentation
normal-cover route supplies every quotient-socle bound, and the checked
literal orbit witness supplies the natural module bound. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow9FinitePackage

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

noncomputable def finiteData :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoZeroSixteenInterfaces.row9 :=
  .ofCertificates
    PrimitiveAffineDegreeTwoZeroSixteenRows9And11AugmentationSocles.row9Socle
    PrimitiveAffineDegreeTwoZeroSixteenRow9OrbitWitness.natural

noncomputable def catalogueFiniteData :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.zero16 (8 : Fin 29)) :=
  finiteData

noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization DegreeTwoZeroSixteenInterfaces.row9 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoZeroSixteenInterfaces.row9
      degreeTwoSixteenPairProfiles p :=
  finiteData.resolvedRow hZmud lit R

end PrimitiveAffineDegreeTwoZeroSixteenRow9FinitePackage
end SymmetricSubgroupAsymptotics

end

