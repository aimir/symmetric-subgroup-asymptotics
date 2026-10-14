import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23NormalCertificate

/-! # Literal paired-eight top 14, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top14 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow23TopCertificate.Source :=
    PrimitiveAffineEightFrameRow23TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow23NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow23NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow23NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow23NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow23TopCertificate.generators))
    PrimitiveAffineEightFrameRow23TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
