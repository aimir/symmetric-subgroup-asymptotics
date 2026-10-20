import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop15NormalCertificate

/-! # Literal paired-eight top 15, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top15 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameTop15TopCertificate.Source :=
    PrimitiveAffineEightFrameTop15TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameTop15NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameTop15NormalCertificate.topAmbient
    PrimitiveAffineEightFrameTop15NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameTop15NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameTop15TopCertificate.generators))
    PrimitiveAffineEightFrameTop15TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
