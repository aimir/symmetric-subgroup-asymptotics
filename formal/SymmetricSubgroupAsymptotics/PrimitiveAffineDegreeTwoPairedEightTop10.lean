import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop10NormalCertificate

/-! # Literal paired-eight top 10, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top10 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameTop10TopCertificate.Source :=
    PrimitiveAffineEightFrameTop10TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameTop10NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameTop10NormalCertificate.topAmbient
    PrimitiveAffineEightFrameTop10NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameTop10NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameTop10TopCertificate.generators))
    PrimitiveAffineEightFrameTop10TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
