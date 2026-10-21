import SymmetricSubgroupAsymptotics.Row278OriginalJointData
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixActualNormalConsumers
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.ProductTwoPrimitiveSixSoclesDirectConsumers

/-! Isolated direct six-point and coarse twelve-point consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics.Row278OriginalBlockFrame

namespace DirectConsumers

open Non2UnipotentPrefixFiniteMenu

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

open DegreeTwoTwelvePairFiniteCatalogue

theorem quotientSocle_three
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (N : Subgroup Original) [N.Normal] : SocleNormalGeneratorBound (Original ⧸ N) 3 :=
  _root_.SymmetricSubgroupAsymptotics.ProductBlockFrame.DirectConsumers.quotientSocle_three_of_two_primitive_six_components
    socle catalogue blockFrame top_surjective N

def quotientFamily
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    row278Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row278Interface.normalRegistry (fun N => by
      letI := N.2
      exact _root_.SymmetricSubgroupAsymptotics.Row278OriginalBlockFrame.DirectConsumers.quotientSocle_three socle catalogue N.1)

def jointData
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row278Interface 3 1 where
  topSocle := _root_.SymmetricSubgroupAsymptotics.Row278OriginalBlockFrame.DirectConsumers.quotientFamily socle catalogue
  natural := PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily.row278Natural

def flexibleData
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    DegreeTwoTwelveFlexibleProfiles.Data row278Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact (_root_.SymmetricSubgroupAsymptotics.Row278OriginalBlockFrame.DirectConsumers.jointData socle catalogue) (by decide +kernel)

end DirectConsumers

end SymmetricSubgroupAsymptotics.Row278OriginalBlockFrame

