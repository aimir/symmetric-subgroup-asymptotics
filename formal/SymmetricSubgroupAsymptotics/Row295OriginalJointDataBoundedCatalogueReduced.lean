import SymmetricSubgroupAsymptotics.Row295OriginalJointData
import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveNormalConsumerFacts
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.PrimitiveTwelveFinalPublishedNormalGeneratorsBoundedCatalogueReduced

/-! Isolated actual degree6/12 normal-consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

set_option maxRecDepth 8192

noncomputable section

namespace SymmetricSubgroupAsymptotics.Row295OriginalJointData

namespace BoundedCatalogueReduced

open Non2UnipotentPrefixFiniteMenu

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

open DegreeTwoTwelvePairFiniteCatalogue

theorem quotientSocle
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (N : Subgroup Row295Top) [N.Normal] : SocleNormalGeneratorBound (Row295Top ⧸ N) 1 :=
  _root_.SymmetricSubgroupAsymptotics.PrimitiveTwelveFinalPublishedNormalGenerators.BoundedCatalogueReduced.quotientSocle_one socle primitiveCatalogue Row295Top N

def jointData (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row295Interface 1 1 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds _ (fun N => by
    letI := N.2
    exact _root_.SymmetricSubgroupAsymptotics.Row295OriginalJointData.BoundedCatalogueReduced.quotientSocle socle primitiveCatalogue N.1)
  natural := Row295OriginalElevenCycleNatural.natural

def flexibleData (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveFlexibleProfiles.Data row295Interface :=
  .ofExact (_root_.SymmetricSubgroupAsymptotics.Row295OriginalJointData.BoundedCatalogueReduced.jointData socle primitiveCatalogue) (by decide +kernel)

end BoundedCatalogueReduced

end SymmetricSubgroupAsymptotics.Row295OriginalJointData

