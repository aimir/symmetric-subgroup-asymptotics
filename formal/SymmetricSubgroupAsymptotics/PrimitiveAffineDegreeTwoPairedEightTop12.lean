import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21NormalCertificate

/-! # Literal paired-eight top 12, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top12 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow21TopCertificate.Source :=
    PrimitiveAffineEightFrameRow21TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow21NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow21NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow21NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow21NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow21TopCertificate.generators))
    PrimitiveAffineEightFrameRow21TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
