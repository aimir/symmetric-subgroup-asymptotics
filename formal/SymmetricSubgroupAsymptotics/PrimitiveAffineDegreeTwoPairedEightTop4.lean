import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3NormalCertificate

/-! # Literal paired-eight top 4, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top4 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow3TopCertificate.Source :=
    PrimitiveAffineEightFrameRow3TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow3NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow3NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow3NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow3NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow3TopCertificate.generators))
    PrimitiveAffineEightFrameRow3TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
