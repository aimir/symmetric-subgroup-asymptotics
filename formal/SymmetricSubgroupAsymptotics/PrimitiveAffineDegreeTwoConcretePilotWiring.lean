import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoConcreteResidualAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow1Resolution
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow3Resolution
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow1Resolution
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopRelativeKernelOrbitRows

/-!
# Concrete pilot wiring in the degree-two residual source

The first count-twelve row, the first paired-eight row, and the third
primitive count-sixteen row already have checked finite certificates.  This
file wires those endpoints into the literal catalogues.  Consequently the
remaining semantic input cannot replace any pilot with a project-owned row
premise.  The paired-eight slot retains only the two literal representation
inequalities on raw omega fixed vectors and nonfixed simple rows; its
Schur-capacity predicate, prefix, relative characters, and resolved row are
constructed here.

The resulting constructor still exposes the unresolved catalogue rows, but
its type records strict progress toward the complete concrete degree-two
source: count-twelve row index `0`, paired-eight row index `0`, and
primitive-sixteen row index `2` are wired to their generated certificates.
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
namespace PairedEightPilot := PrimitiveAffineDegreeTwoPairedEightRow1Resolution

abbrev TwelveCatalogue := Concrete.TwelveCatalogue
abbrev SixteenCatalogue := Concrete.SixteenCatalogue

/-- Semantic data for precisely the rows not covered by the three checked
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
      j ≠ (0 : Fin 24) →
      DegreeTwoPairTopTowerRelativeKernelOrbitRowData
        (SixteenCatalogue.paired8 j)
        degreeTwoSixteenPairProfiles p realization
  sixteenPaired8Row1Fixed :
    ∀ (p : PreE7PairActionClass 16)
      (realization : DegreeTwoPairTopTowerRealization
        (SixteenCatalogue.paired8 (0 : Fin 24)) p)
      (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}),
      Module.finrank (ZMod 2)
          (binaryKernelOmegaConjugationRepresentation
            (realization.rawQuotientMap N)).invariants ≤
        (PrimitiveAffineDegreeTwoPairedEightRow1CoupledHeads.
          towerCoupledHeadData realization).omegaHeadDemand N
  sixteenPaired8Row1Nonfixed :
    ∀ (p : PreE7PairActionClass 16)
      (realization : DegreeTwoPairTopTowerRealization
        (SixteenCatalogue.paired8 (0 : Fin 24)) p)
      (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal})
      (X : Submodule (ZMod 2)[preE7PairAction 16 p ⫽ N.1]
        (PairedEightPilot.OmegaSocleRepresentation realization N).asModule),
      [IsSimpleModule (ZMod 2)[preE7PairAction 16 p ⫽ N.1] X] →
      ¬ representationSubmoduleFixed
          (PairedEightPilot.OmegaSocleRepresentation realization N) X →
      schurSocleMultiplicity
          (k := ZMod 2)
          (R := (ZMod 2)[preE7PairAction 16 p ⫽ N.1])
          (A := (PairedEightPilot.OmegaSocleRepresentation
            realization N).asModule) (X := X) ≤
        3 * Module.finrank
          (Module.End (ZMod 2)[preE7PairAction 16 p ⫽ N.1] X) X
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

/-- Count-sixteen resolution with paired-eight row index `0` and primitive
row index `2` supplied by their checked finite certificates. -/
noncomputable def sixteenResolution
    (D : RemainingPairTopSemanticData)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) :
    DegreeTwoSixteenPairTopCatalogueResolution SixteenCatalogue where
  paired8 j p realization := by
    by_cases hj : j = (0 : Fin 24)
    · subst j
      exact PairedEightPilot.resolvedRow hZmud lit realization
        (PairedEightPilot.omegaSocleSchurCapacityLeFour_of_rawCoupled_nonfixed
          realization
          (D.sixteenPaired8Row1Fixed p realization)
          (D.sixteenPaired8Row1Nonfixed p realization))
    · exact ((D.sixteenPaired8 j p realization hj).sixteenResolvedData
        lit).toResolvedRow
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

/-- Degree-two residual source with all three checked catalogue pilots
installed at their literal indices.  The remaining structure excludes the
full row objects at those positions. -/
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
