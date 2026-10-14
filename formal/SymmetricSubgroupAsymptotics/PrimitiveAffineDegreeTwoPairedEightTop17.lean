import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop17NormalCertificate

/-! # Literal paired-eight top 17, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top17 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameTop17TopCertificate.Source :=
    PrimitiveAffineEightFrameTop17TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameTop17NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameTop17NormalCertificate.topAmbient
    PrimitiveAffineEightFrameTop17NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameTop17NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameTop17TopCertificate.generators))
    PrimitiveAffineEightFrameTop17TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
