import SymmetricSubgroupAsymptotics.Rows228229OriginalJointData
import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveNormalConsumerFacts
import Mathlib.Tactic.FinCases

/-! Isolated actual degree6/12 normal-consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics.Rows228229ActualQuartetCoordinates

namespace BoundedCatalogueReduced

open Non2UnipotentPrefixFiniteMenu

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

open DegreeTwoTwelvePairFiniteCatalogue

open BinaryPlaneWreathIrreducible

private def row228Joint :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row228Interface 3 1 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row228Interface.normalRegistry (fun N => by letI := N.2; exact quotientSocle_three 0 N.1)
  natural := PrimitiveAffineDegreeTwoTwelveTwistedAlternatingNaturalFamily.row228Natural

private def row229Joint :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row229Interface 3 1 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row229Interface.normalRegistry (fun N => by letI := N.2; exact quotientSocle_three 1 N.1)
  natural := PrimitiveAffineDegreeTwoTwelveDiagonalAlternatingNaturalFamily.row229Natural

def row228Data (_socle : PublishedPrimitiveSocleDichotomyInput)
    (_catalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveFlexibleProfiles.Data row228Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact row228Joint (by decide +kernel)

def row229Data (_socle : PublishedPrimitiveSocleDichotomyInput)
    (_catalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveFlexibleProfiles.Data row229Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact row229Joint (by decide +kernel)

end BoundedCatalogueReduced

end SymmetricSubgroupAsymptotics.Rows228229ActualQuartetCoordinates

