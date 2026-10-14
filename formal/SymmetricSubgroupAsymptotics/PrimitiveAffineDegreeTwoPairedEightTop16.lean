import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop16NormalCertificate

/-! # Literal paired-eight top 16, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top16 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameTop16TopCertificate.Source :=
    PrimitiveAffineEightFrameTop16TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameTop16NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameTop16NormalCertificate.topAmbient
    PrimitiveAffineEightFrameTop16NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameTop16NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameTop16TopCertificate.generators))
    PrimitiveAffineEightFrameTop16TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
