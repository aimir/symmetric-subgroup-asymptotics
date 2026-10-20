import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1NormalCertificate

/-! # Literal paired-eight top 2, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top2 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow1TopCertificate.Source :=
    PrimitiveAffineEightFrameRow1TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow1NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow1NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow1NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow1NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow1TopCertificate.generators))
    PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
