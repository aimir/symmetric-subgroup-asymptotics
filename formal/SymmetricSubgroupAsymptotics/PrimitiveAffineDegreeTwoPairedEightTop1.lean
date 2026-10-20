import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0NormalCertificate

/-! # Literal paired-eight top 1, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top1 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow0TopCertificate.Source :=
    PrimitiveAffineEightFrameRow0TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow0NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow0NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow0NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow0NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow0TopCertificate.generators))
    PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
