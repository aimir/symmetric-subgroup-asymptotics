import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20NormalCertificate

/-! # Literal paired-eight top 11, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top11 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow20TopCertificate.Source :=
    PrimitiveAffineEightFrameRow20TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow20NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow20NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow20NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow20NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow20TopCertificate.generators))
    PrimitiveAffineEightFrameRow20TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
