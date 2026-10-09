import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoConcreteResidualAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow1Resolution
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow3Resolution
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopRelativeKernelOrbitRows

/-!
# Concrete pilot wiring in the degree-two residual source

The first count-twelve row and the third primitive count-sixteen row already
have checked quotient-socle and natural-module certificates.  This file wires
those endpoints into the literal catalogues.  Consequently the remaining
semantic input cannot replace either pilot with a project-owned row premise.

The resulting constructor still exposes the unresolved catalogue rows, but
its type records the strict progress toward the complete concrete degree-two
source: count-twelve row index `0` and primitive-sixteen row index `2` are
discharged by their generated finite certificates.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoConcretePilotWiring

namespace Concrete := DegreeTwoConcreteResidualAssembly
namespace TwelvePilot := PrimitiveAffineDegreeTwoTwelveRow1Resolution
namespace SixteenPilot := PrimitiveAffineDegreeTwoPrimitiveSixteenRow3Resolution

abbrev TwelveCatalogue := Concrete.TwelveCatalogue
abbrev SixteenCatalogue := Concrete.SixteenCatalogue

/-- Semantic data for precisely the rows not covered by the two checked
pilots.  The disequality hypotheses prevent the pilot rows from reappearing
as abstract assumptions. -/
structure RemainingPairTopSemanticData : Type 1 where
  twelveRelative :
    ∀ (j : Fin 301) (p : PreE7PairActionClass 12)
      (realization : DegreeTwoPairTopRealization
        (TwelveCatalogue.row j).finite p),
      j ≠ (0 : Fin 301) →
      (TwelveCatalogue.row j).branch ≠ .ternary →
      DegreeTwoPairTopRelativeKernelOrbitRowData
        (TwelveCatalogue.row j).finite
        (TwelveCatalogue.row j).expectedProfiles p realization
  twelveTernary :
    ∀ (j : Fin 301) (p : PreE7PairActionClass 12),
      DegreeTwoPairTopRealization (TwelveCatalogue.row j).finite p →
      (TwelveCatalogue.row j).branch = .ternary →
      DegreeTwoTwelveTernaryComparatorData p
  sixteenPaired8 :
    ∀ (j : Fin 24) (p : PreE7PairActionClass 16)
      (realization : DegreeTwoPairTopTowerRealization
        (SixteenCatalogue.paired8 j) p),
      DegreeTwoPairTopTowerRelativeKernelOrbitRowData
        (SixteenCatalogue.paired8 j)
        degreeTwoSixteenPairProfiles p realization
  sixteenZero16 :
    ∀ (j : Fin 29) (p : PreE7PairActionClass 16)
      (realization : DegreeTwoPairTopRealization
        (SixteenCatalogue.zero16 j) p),
      DegreeTwoPairTopRelativeKernelOrbitRowData
        (SixteenCatalogue.zero16 j)
        degreeTwoSixteenPairProfiles p realization
  sixteenTwoAffine16 :
    ∀ (j : Fin 15) (p : PreE7PairActionClass 16)
      (realization : DegreeTwoPairTopRealization
        (SixteenCatalogue.twoAffine16 j) p),
      DegreeTwoPairTopRelativeKernelOrbitRowData
        (SixteenCatalogue.twoAffine16 j)
        degreeTwoSixteenPairProfiles p realization
  sixteenPrimitive16 :
    ∀ (j : Fin 20) (p : PreE7PairActionClass 16)
      (realization : DegreeTwoPairTopRealization
        (SixteenCatalogue.primitive16 j) p),
      j ≠ (2 : Fin 20) →
      DegreeTwoPairTopRelativeKernelOrbitRowData
        (SixteenCatalogue.primitive16 j)
        degreeTwoSixteenPairProfiles p realization
  sixteenNatural :
    ∀ (kind : DegreeTwoSixteenNaturalTop)
      (p : PreE7PairActionClass 16)
      (realization : DegreeTwoSixteenNaturalTopRealization kind p),
      DegreeTwoSixteenNaturalSocleGeneratorData kind p realization

namespace RemainingPairTopSemanticData

/-- Count-twelve resolution with row index `0` supplied by the checked
row-one quotient-socle and natural-module certificates. -/
noncomputable def twelveResolution
    (D : RemainingPairTopSemanticData)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) :
    DegreeTwoTwelvePairTopCatalogueResolution TwelveCatalogue := by
  intro j p realization
  by_cases hj : j = (0 : Fin 301)
  · subst j
    exact TwelvePilot.resolvedRow hZmud lit realization
  · by_cases hbranch : (TwelveCatalogue.row j).branch = .ternary
    · exact (D.twelveTernary j p realization hbranch).resolvedRow
    · exact ((D.twelveRelative j p realization hj hbranch).twelveResolvedData
        lit).toResolvedRow

/-- Count-sixteen resolution with primitive row index `2` supplied by the
checked row-three quotient-socle and natural-module certificates. -/
noncomputable def sixteenResolution
    (D : RemainingPairTopSemanticData)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) :
    DegreeTwoSixteenPairTopCatalogueResolution SixteenCatalogue where
  paired8 j p realization :=
    ((D.sixteenPaired8 j p realization).sixteenResolvedData lit).toResolvedRow
  zero16 j p realization :=
    ((D.sixteenZero16 j p realization).sixteenResolvedData lit).toResolvedRow
  twoAffine16 j p realization :=
    ((D.sixteenTwoAffine16 j p realization).sixteenResolvedData lit).toResolvedRow
  primitive16 j p realization := by
    by_cases hj : j = (2 : Fin 20)
    · subst j
      exact SixteenPilot.resolvedRow hZmud lit realization
    · exact ((D.sixteenPrimitive16 j p realization hj).sixteenResolvedData
        lit).toResolvedRow
  natural kind p realization :=
    (D.sixteenNatural kind p realization).source hZmud lit

end RemainingPairTopSemanticData

/-- Degree-two residual source with both checked catalogue pilots installed
at their literal indices.  Only the other 300 relative/comparator positions
and the other 19 primitive-sixteen positions occur in `remaining`. -/
noncomputable def source
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (publishedThree :
      PublishedDegreeTwoThreePairRepresentativeClassification)
    (publishedFour : PublishedDegreeTwoFourPairClassification)
    (sixPairTable : PrimitiveAffineDegreeTwoSixPairOwnerTable)
    (publishedSix : PublishedDegreeTwoSixPairCatalogueLocator sixPairTable)
    (eightPairTable : DegreeTwoEightPairFiniteCatalogue)
    (publishedEight :
      PublishedDegreeTwoEightPairCatalogueLocator eightPairTable)
    (publishedTwelve : Concrete.PublishedTwelveCatalogueLocator)
    (publishedSixteen : Concrete.PublishedSixteenCatalogueLocator)
    (remaining : RemainingPairTopSemanticData) :
    PrimitiveAffineResidualDegreeSource 2 :=
  degreeTwoResidualSource_of_finitePairTopCatalogues
    hZmud lit publishedThree publishedFour sixPairTable publishedSix
    eightPairTable publishedEight
    TwelveCatalogue publishedTwelve
      (remaining.twelveResolution hZmud lit)
    SixteenCatalogue publishedSixteen
      (remaining.sixteenResolution hZmud lit)

end DegreeTwoConcretePilotWiring
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
