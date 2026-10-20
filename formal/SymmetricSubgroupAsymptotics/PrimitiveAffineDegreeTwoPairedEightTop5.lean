import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4NormalCertificate

/-! # Literal paired-eight top 5, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top5 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow4TopCertificate.Source :=
    PrimitiveAffineEightFrameRow4TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow4NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow4NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow4NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow4NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow4TopCertificate.generators))
    PrimitiveAffineEightFrameRow4TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
