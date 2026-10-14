import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29NormalCertificate

/-! # Literal paired-eight top 22, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top22 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow29TopCertificate.Source :=
    PrimitiveAffineEightFrameRow29TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow29NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow29NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow29NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow29NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow29TopCertificate.generators))
    PrimitiveAffineEightFrameRow29TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
