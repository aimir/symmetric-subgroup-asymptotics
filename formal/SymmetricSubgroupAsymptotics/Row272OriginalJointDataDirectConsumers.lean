import SymmetricSubgroupAsymptotics.Row272OriginalJointData
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixActualNormalConsumers
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.PrimitiveTwelveActualQuotientSocleThree

/-! Isolated direct six-point and coarse twelve-point consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

set_option maxRecDepth 8192

noncomputable section

namespace SymmetricSubgroupAsymptotics.Row272OriginalJointData

namespace DirectConsumers

open Non2UnipotentPrefixFiniteMenu

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

open DegreeTwoTwelvePairFiniteCatalogue

theorem quotientSocle
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (N : Subgroup Row272Top) [N.Normal] : SocleNormalGeneratorBound (Row272Top ⧸ N) 3 :=
  PrimitiveSocleRawStructure.primitive_degreeTwelve_quotientSocle_three primitiveCatalogue N

def jointData (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row272Interface 3 1 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds _ (fun N => by
    letI := N.2
    exact _root_.SymmetricSubgroupAsymptotics.Row272OriginalJointData.DirectConsumers.quotientSocle socle primitiveCatalogue N.1)
  natural := Row272OriginalElevenCycleNatural.natural

def flexibleData (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    DegreeTwoTwelveFlexibleProfiles.Data row272Interface :=
  .ofExact (_root_.SymmetricSubgroupAsymptotics.Row272OriginalJointData.DirectConsumers.jointData socle primitiveCatalogue) (by decide +kernel)

end DirectConsumers

end SymmetricSubgroupAsymptotics.Row272OriginalJointData

