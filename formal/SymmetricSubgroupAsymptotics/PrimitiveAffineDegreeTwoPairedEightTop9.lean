import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop9NormalCertificate

/-! # Literal paired-eight top 9, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top9 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameTop9TopCertificate.Source :=
    PrimitiveAffineEightFrameTop9TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameTop9NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameTop9NormalCertificate.topAmbient
    PrimitiveAffineEightFrameTop9NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameTop9NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameTop9TopCertificate.generators))
    PrimitiveAffineEightFrameTop9TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
