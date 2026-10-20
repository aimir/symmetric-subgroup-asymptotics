import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2NormalCertificate

/-! # Literal paired-eight top 3, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top3 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow2TopCertificate.Source :=
    PrimitiveAffineEightFrameRow2TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow2NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow2NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow2NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow2NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow2TopCertificate.generators))
    PrimitiveAffineEightFrameRow2TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
