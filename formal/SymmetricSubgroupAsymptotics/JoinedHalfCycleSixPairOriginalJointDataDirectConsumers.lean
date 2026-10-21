import SymmetricSubgroupAsymptotics.JoinedHalfCycleSixPairOriginalJointData
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixActualNormalConsumers
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.OriginalSixPairNaturalJointDataDirectConsumers

/-! Isolated direct six-point and coarse twelve-point consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics.JoinedHalfCycleSixPairOriginalJointData

namespace DirectConsumers

open Non2UnipotentPrefixFiniteMenu

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

open DegreeTwoTwelvePairFiniteCatalogue

def row208Data (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    DegreeTwoTwelveFlexibleProfiles.Data row208Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (_root_.SymmetricSubgroupAsymptotics.OriginalSixPairNaturalJointData.DirectConsumers.jointData socle catalogue row208Interface row208Frame
      PrimitiveAffineDegreeTwoTwelveJoinedHalfCycleNaturalFamily.row208Natural) (by decide +kernel)

def row260Data (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    DegreeTwoTwelveFlexibleProfiles.Data row260Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (_root_.SymmetricSubgroupAsymptotics.OriginalSixPairNaturalJointData.DirectConsumers.jointData socle catalogue row260Interface row260Frame
      PrimitiveAffineDegreeTwoTwelveJoinedHalfCycleNaturalFamily.row260Natural) (by decide +kernel)

end DirectConsumers

end SymmetricSubgroupAsymptotics.JoinedHalfCycleSixPairOriginalJointData

