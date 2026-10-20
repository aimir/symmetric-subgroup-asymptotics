import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop13NormalCertificate

/-! # Literal paired-eight top 13, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top13 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameTop13TopCertificate.Source :=
    PrimitiveAffineEightFrameTop13TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameTop13NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameTop13NormalCertificate.topAmbient
    PrimitiveAffineEightFrameTop13NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameTop13NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameTop13TopCertificate.generators))
    PrimitiveAffineEightFrameTop13TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
