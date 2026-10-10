import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoConcreteResidualAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow1Resolution
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow3Resolution
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightCoupledCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopRelativeKernelOrbitRows

/-!
# Concrete pilot wiring in the degree-two residual source

Every joint count-twelve row, every paired-eight row, and the third primitive
count-sixteen row are routed through concrete finite certificates.  This
file wires those endpoints into the literal catalogues.  Consequently the
remaining semantic input cannot replace any of those families with a
project-owned row premise.  The 283 joint count-twelve rows are constructed
uniformly from quotient-socle and natural-module declarations; the
paired-eight rows are constructed uniformly from their three finite
declarations.

The resulting constructor still exposes the exceptional count-twelve and
unresolved count-sixteen families, but all generic count-twelve rows, all
paired-eight rows, and primitive-sixteen row index `2` are wired to finite
certificates.
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
namespace PairedEightFinite := DegreeTwoPairedEightFiniteCatalogueData
namespace TwelveJointFinite := DegreeTwoTwelveJointFiniteRows
namespace TwelveJointCatalogue :=
  DegreeTwoTwelveJointFiniteRows.LiteralCatalogue
namespace TwelveFiniteCatalogue := DegreeTwoTwelvePairFiniteCatalogue

abbrev TwelveCatalogue := Concrete.TwelveCatalogue
abbrev SixteenCatalogue := Concrete.SixteenCatalogue

/-- Semantic and finite data for the rows not already generated.  Joint
count-twelve and paired-eight rows accept only finite declarations on their
literal tops.  The count-twelve semantic field is restricted to the ten
core-or-paired exceptional rows.  The disequality on primitive-sixteen
prevents its generated pilot from reappearing as an abstract assumption. -/
structure RemainingPairTopSemanticData : Type 1 where
  twelveJoint :
    TwelveJointCatalogue.RemainingDegreeTwoTwelveJointFiniteRowData
  twelveExceptional :
    ∀ (j : Fin 301) (p : PreE7PairActionClass 12)
      (realization : DegreeTwoPairTopRealization
        (TwelveCatalogue.row j).finite p),
      (TwelveCatalogue.row j).branch ≠ .joint →
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
    RemainingDegreeTwoPairedEightFiniteRowData
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

/-- Count-twelve resolution with all 283 joint rows supplied by the generic
finite Schur package.  The generated row-one package is inserted before
catalogue dispatch. -/
noncomputable def twelveResolution
    (D : RemainingPairTopSemanticData)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) :
    DegreeTwoTwelvePairTopCatalogueResolution TwelveCatalogue := by
  let jointFinite :
      TwelveJointFinite.DegreeTwoTwelveJointFiniteCatalogueData
        TwelveCatalogue :=
    TwelveJointCatalogue.ofGeneratedRow1 TwelvePilot.finiteData D.twelveJoint
  intro j p realization
  by_cases hjoint : (TwelveCatalogue.row j).branch = .joint
  · exact jointFinite.resolvedRow hZmud lit
      (fun i hi ↦ TwelveFiniteCatalogue.joint_parameters i hi)
      j realization hjoint
  · by_cases hternary : (TwelveCatalogue.row j).branch = .ternary
    · exact (D.twelveTernary j p realization hternary).resolvedRow
    · let row := D.twelveExceptional j p realization hjoint hternary
      exact (row.twelveResolvedData lit).toResolvedRow

/-- Count-sixteen resolution with every paired-eight row and primitive row
index `2` supplied by finite certificates. -/
noncomputable def sixteenResolution
    (D : RemainingPairTopSemanticData)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) :
    DegreeTwoSixteenPairTopCatalogueResolution SixteenCatalogue where
  paired8 j p realization := by
    exact (((PairedEightFinite.ofGeneratedRow1 D.sixteenPaired8).
      rowData hZmud j realization).sixteenResolvedData lit).toResolvedRow
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

/-- Degree-two residual source with the checked catalogue pilots and the
uniform joint-twelve and paired-eight finite dispatch installed at their
literal indices.  The remaining structure excludes semantic row objects for
both complete families. -/
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
