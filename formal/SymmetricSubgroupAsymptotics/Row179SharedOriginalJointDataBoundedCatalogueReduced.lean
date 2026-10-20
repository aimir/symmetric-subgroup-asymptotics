import SymmetricSubgroupAsymptotics.Row179SharedOriginalJointData
import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveNormalConsumerFacts
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.PrimitiveTwelveFinalPublishedNormalGeneratorsBoundedCatalogueReduced

/-! Isolated actual degree6/12 normal-consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics.Row179SharedOriginalJointData

namespace BoundedCatalogueReduced

open Non2UnipotentPrefixFiniteMenu

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

open DegreeTwoTwelvePairFiniteCatalogue

theorem row179_quotientSocle
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (N : Subgroup Row179Top) [N.Normal] : SocleNormalGeneratorBound (Row179Top ⧸ N) 1 :=
  _root_.SymmetricSubgroupAsymptotics.PrimitiveTwelveFinalPublishedNormalGenerators.BoundedCatalogueReduced.quotientSocle_one socle catalogue Row179Top N

theorem row218_quotientSocle
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (N : Subgroup Row218Top) [N.Normal] : SocleNormalGeneratorBound (Row218Top ⧸ N) 1 :=
  _root_.SymmetricSubgroupAsymptotics.PrimitiveTwelveFinalPublishedNormalGenerators.BoundedCatalogueReduced.quotientSocle_one socle catalogue Row218Top N

def row179Family
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    row179Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row179Interface.normalRegistry (fun N => by letI := N.2; exact _root_.SymmetricSubgroupAsymptotics.Row179SharedOriginalJointData.BoundedCatalogueReduced.row179_quotientSocle socle catalogue N.1)

def row218Family
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    row218Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row218Interface.normalRegistry (fun N => by letI := N.2; exact _root_.SymmetricSubgroupAsymptotics.Row179SharedOriginalJointData.BoundedCatalogueReduced.row218_quotientSocle socle catalogue N.1)

def row179Data
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row179Interface 1 1 where
  topSocle := _root_.SymmetricSubgroupAsymptotics.Row179SharedOriginalJointData.BoundedCatalogueReduced.row179Family socle catalogue
  natural := PrimitiveAffineDegreeTwoTwelveElevenCycleNaturalFamily.row179Natural

def row218Data
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row218Interface 1 1 where
  topSocle := _root_.SymmetricSubgroupAsymptotics.Row179SharedOriginalJointData.BoundedCatalogueReduced.row218Family socle catalogue
  natural := PrimitiveAffineDegreeTwoTwelveElevenCycleNaturalFamily.row218Natural

def row179Flexible
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveFlexibleProfiles.Data row179Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact (_root_.SymmetricSubgroupAsymptotics.Row179SharedOriginalJointData.BoundedCatalogueReduced.row179Data socle catalogue) (by decide +kernel)

def row218Flexible
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveFlexibleProfiles.Data row218Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact (_root_.SymmetricSubgroupAsymptotics.Row179SharedOriginalJointData.BoundedCatalogueReduced.row218Data socle catalogue) (by decide +kernel)

end BoundedCatalogueReduced

end SymmetricSubgroupAsymptotics.Row179SharedOriginalJointData

