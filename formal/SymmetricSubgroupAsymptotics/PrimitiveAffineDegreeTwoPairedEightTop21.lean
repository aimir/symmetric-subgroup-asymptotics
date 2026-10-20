import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow28NormalCertificate

/-! # Literal paired-eight top 21, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top21 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow28TopCertificate.Source :=
    PrimitiveAffineEightFrameRow28TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow28NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow28NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow28NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow28NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow28TopCertificate.generators))
    PrimitiveAffineEightFrameRow28TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
