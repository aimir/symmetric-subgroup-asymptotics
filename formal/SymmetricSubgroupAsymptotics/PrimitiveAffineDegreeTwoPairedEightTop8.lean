import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop8NormalCertificate

/-! # Literal paired-eight top 8, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top8 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameTop8TopCertificate.Source :=
    PrimitiveAffineEightFrameTop8TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameTop8NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameTop8NormalCertificate.topAmbient
    PrimitiveAffineEightFrameTop8NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameTop8NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameTop8TopCertificate.generators))
    PrimitiveAffineEightFrameTop8TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
