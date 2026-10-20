import SymmetricSubgroupAsymptotics.Row272OriginalJointData
import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveNormalConsumerFacts
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.PrimitiveTwelveFinalPublishedNormalGeneratorsBoundedCatalogueReduced

/-! Isolated actual degree6/12 normal-consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

set_option maxRecDepth 8192

noncomputable section

namespace SymmetricSubgroupAsymptotics.Row272OriginalJointData

namespace BoundedCatalogueReduced

open Non2UnipotentPrefixFiniteMenu

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

open DegreeTwoTwelvePairFiniteCatalogue

theorem quotientSocle
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (N : Subgroup Row272Top) [N.Normal] : SocleNormalGeneratorBound (Row272Top ⧸ N) 1 :=
  _root_.SymmetricSubgroupAsymptotics.PrimitiveTwelveFinalPublishedNormalGenerators.BoundedCatalogueReduced.quotientSocle_one socle primitiveCatalogue Row272Top N

def jointData (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row272Interface 1 1 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds _ (fun N => by
    letI := N.2
    exact _root_.SymmetricSubgroupAsymptotics.Row272OriginalJointData.BoundedCatalogueReduced.quotientSocle socle primitiveCatalogue N.1)
  natural := Row272OriginalElevenCycleNatural.natural

def flexibleData (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveFlexibleProfiles.Data row272Interface :=
  .ofExact (_root_.SymmetricSubgroupAsymptotics.Row272OriginalJointData.BoundedCatalogueReduced.jointData socle primitiveCatalogue) (by decide +kernel)

end BoundedCatalogueReduced

end SymmetricSubgroupAsymptotics.Row272OriginalJointData

