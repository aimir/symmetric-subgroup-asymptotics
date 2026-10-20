import SymmetricSubgroupAsymptotics.JoinedHalfCycleSixPairOriginalJointData
import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveNormalConsumerFacts
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.OriginalSixPairNaturalJointDataBoundedCatalogueReduced

/-! Isolated actual degree6/12 normal-consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics.JoinedHalfCycleSixPairOriginalJointData

namespace BoundedCatalogueReduced

open Non2UnipotentPrefixFiniteMenu

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

open DegreeTwoTwelvePairFiniteCatalogue

def row208Data (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveFlexibleProfiles.Data row208Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (_root_.SymmetricSubgroupAsymptotics.OriginalSixPairNaturalJointData.BoundedCatalogueReduced.jointData socle catalogue row208Interface row208Frame
      PrimitiveAffineDegreeTwoTwelveJoinedHalfCycleNaturalFamily.row208Natural) (by decide +kernel)

def row260Data (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveFlexibleProfiles.Data row260Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (_root_.SymmetricSubgroupAsymptotics.OriginalSixPairNaturalJointData.BoundedCatalogueReduced.jointData socle catalogue row260Interface row260Frame
      PrimitiveAffineDegreeTwoTwelveJoinedHalfCycleNaturalFamily.row260Natural) (by decide +kernel)

end BoundedCatalogueReduced

end SymmetricSubgroupAsymptotics.JoinedHalfCycleSixPairOriginalJointData

