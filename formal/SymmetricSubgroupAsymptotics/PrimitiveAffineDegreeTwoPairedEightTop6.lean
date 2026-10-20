import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8NormalCertificate

/-! # Literal paired-eight top 6, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top6 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow8TopCertificate.Source :=
    PrimitiveAffineEightFrameRow8TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow8NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow8NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow8NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow8NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow8TopCertificate.generators))
    PrimitiveAffineEightFrameRow8TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
