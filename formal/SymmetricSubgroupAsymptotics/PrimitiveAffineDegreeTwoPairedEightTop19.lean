import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27NormalCertificate

/-! # Literal paired-eight top 19, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top19 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow27TopCertificate.Source :=
    PrimitiveAffineEightFrameRow27TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow27NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow27NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow27NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow27NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow27TopCertificate.generators))
    PrimitiveAffineEightFrameRow27TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
