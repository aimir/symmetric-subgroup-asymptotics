import SymmetricSubgroupAsymptotics.Row295OriginalJointData
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixActualNormalConsumers
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.PrimitiveTwelveActualQuotientSocleThree

/-! Isolated direct six-point and coarse twelve-point consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

set_option maxRecDepth 8192

noncomputable section

namespace SymmetricSubgroupAsymptotics.Row295OriginalJointData

namespace DirectConsumers

open Non2UnipotentPrefixFiniteMenu

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

open DegreeTwoTwelvePairFiniteCatalogue

theorem quotientSocle
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (N : Subgroup Row295Top) [N.Normal] : SocleNormalGeneratorBound (Row295Top ⧸ N) 3 :=
  PrimitiveSocleRawStructure.primitive_degreeTwelve_quotientSocle_three primitiveCatalogue N

def jointData (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row295Interface 3 1 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds _ (fun N => by
    letI := N.2
    exact _root_.SymmetricSubgroupAsymptotics.Row295OriginalJointData.DirectConsumers.quotientSocle socle primitiveCatalogue N.1)
  natural := Row295OriginalElevenCycleNatural.natural

def flexibleData (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    DegreeTwoTwelveFlexibleProfiles.Data row295Interface :=
  .ofExact (_root_.SymmetricSubgroupAsymptotics.Row295OriginalJointData.DirectConsumers.jointData socle primitiveCatalogue) (by decide +kernel)

end DirectConsumers

end SymmetricSubgroupAsymptotics.Row295OriginalJointData

