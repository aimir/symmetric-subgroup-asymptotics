import SymmetricSubgroupAsymptotics.Row278OriginalJointData
import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveNormalConsumerFacts
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.ProductTwoPrimitiveSixSoclesBoundedCatalogueReduced

/-! Isolated actual degree6/12 normal-consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics.Row278OriginalBlockFrame

namespace BoundedCatalogueReduced

open Non2UnipotentPrefixFiniteMenu

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

open DegreeTwoTwelvePairFiniteCatalogue

theorem quotientSocle_three
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (N : Subgroup Original) [N.Normal] : SocleNormalGeneratorBound (Original ⧸ N) 3 :=
  _root_.SymmetricSubgroupAsymptotics.ProductBlockFrame.BoundedCatalogueReduced.quotientSocle_three_of_two_primitive_six_components
    socle catalogue blockFrame top_surjective N

def quotientFamily
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    row278Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row278Interface.normalRegistry (fun N => by
      letI := N.2
      exact _root_.SymmetricSubgroupAsymptotics.Row278OriginalBlockFrame.BoundedCatalogueReduced.quotientSocle_three socle catalogue N.1)

def jointData
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row278Interface 3 1 where
  topSocle := _root_.SymmetricSubgroupAsymptotics.Row278OriginalBlockFrame.BoundedCatalogueReduced.quotientFamily socle catalogue
  natural := PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily.row278Natural

def flexibleData
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveFlexibleProfiles.Data row278Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact (_root_.SymmetricSubgroupAsymptotics.Row278OriginalBlockFrame.BoundedCatalogueReduced.jointData socle catalogue) (by decide +kernel)

end BoundedCatalogueReduced

end SymmetricSubgroupAsymptotics.Row278OriginalBlockFrame

