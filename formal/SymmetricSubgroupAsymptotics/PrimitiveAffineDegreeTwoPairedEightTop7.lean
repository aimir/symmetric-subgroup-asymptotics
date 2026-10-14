import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9NormalCertificate

/-! # Literal paired-eight top 7, independent of the catalogue dispatcher -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

noncomputable def top7 : DegreeTwoPairTopFiniteInterface 8 := by
  letI : Group PrimitiveAffineEightFrameRow9TopCertificate.Source :=
    PrimitiveAffineEightFrameRow9TopCertificate.group
  exact DegreeTwoPairTopFiniteInterface.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow9NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow9NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow9NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow9NormalCertificate.data
    (Subgroup.closure
      (Set.range PrimitiveAffineEightFrameRow9TopCertificate.generators))
    PrimitiveAffineEightFrameRow9TopCertificate.originalEquiv

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
