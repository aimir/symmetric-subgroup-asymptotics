import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoConcreteResidualAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow1Resolution
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveExceptionalTemplates
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow3Resolution
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenNaturalFiniteRows
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightCoupledCatalogue

/-!
# Concrete pilot wiring in the degree-two residual source

Every joint count-twelve row, every paired-eight row, and every zero16,
twoAffine16, and primitive16 row is routed through concrete finite
certificates.  The 283 joint count-twelve rows use quotient-socle and
natural-module declarations; the paired-eight rows use their three finite
declarations; and all 64 one-frame count-sixteen rows share the finite
`(2,4)` Schur package.

The natural `A_16`/`S_16` alternative is likewise reduced to two explicit
literal-top packages and one common structural converter.
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
namespace TwelveExceptional := DegreeTwoTwelveExceptionalTemplates
namespace SixteenOneFrameCatalogue := DegreeTwoSixteenOneFrameFiniteRows.Catalogue
namespace SixteenNaturalFinite := DegreeTwoSixteenNaturalFiniteRows

abbrev TwelveCatalogue := Concrete.TwelveCatalogue
abbrev SixteenCatalogue := Concrete.SixteenCatalogue

/-! ## Exact serialized package ledger

After inserting the three checked pilots, the producer boundary consists of
282 joint-twelve packages, 8 core-twelve packages, 2 paired-six packages,
23 paired-eight packages, 29 zero16 packages,
15 twoAffine16 packages, 19 primitive16 packages, and 2 natural-top
packages. -/

/-- Number of explicit packages still assigned to serialized producers. -/
def remainingSerializedPairTopPackageCount : ℕ :=
  282 + 8 + 2 + 23 + 29 + 15 + 19 + 2

@[simp] theorem remainingSerializedPairTopPackageCount_eq :
    remainingSerializedPairTopPackageCount = 380 := by
  norm_num [remainingSerializedPairTopPackageCount]

/-- The count-twelve row-one, paired-eight row-one, primitive16 row-three,
and eight four-ternary compression packages are already present in source. -/
def installedPairTopPilotPackageCount : ℕ := 11

@[simp] theorem completePairTopPackageCount_eq :
    remainingSerializedPairTopPackageCount +
      installedPairTopPilotPackageCount = 391 := by
  norm_num [remainingSerializedPairTopPackageCount,
    installedPairTopPilotPackageCount]

/-- Exact finite data for the rows not already generated.  Each field is a
family of raw literal-top certificates consumed by one of the generic
converters above; no field accepts a resolved row or a project-owned
residual source. -/
structure RemainingPairTopSemanticData : Type 1 where
  twelveJoint :
    TwelveJointCatalogue.RemainingDegreeTwoTwelveJointFiniteRowData
  twelveCorePaired :
    TwelveExceptional.DegreeTwoTwelveCorePairedCatalogueData
  sixteenPaired8 :
    RemainingDegreeTwoPairedEightFiniteRowData
  sixteenOneFrame :
    SixteenOneFrameCatalogue.RemainingDegreeTwoSixteenOneFrameFiniteRowData
  sixteenNatural :
    SixteenNaturalFinite.DegreeTwoSixteenNaturalFiniteCatalogueData

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
  cases hbranch : (TwelveCatalogue.row j).branch with
  | joint =>
    exact jointFinite.resolvedRow hZmud lit
      (fun i hi ↦ TwelveFiniteCatalogue.joint_parameters i hi)
      j realization hbranch
  | core =>
    exact D.twelveCorePaired.coreResolvedRow
      hZmud lit j realization hbranch
  | ternary =>
    exact (degreeTwoFourTernaryCatalogueCompression
      degreeTwoFourTernaryCompressionPackages
      j p realization hbranch).resolvedRow hZmud lit
  | paired =>
    exact D.twelveCorePaired.pairedResolvedRow
      hZmud lit j realization hbranch

/-- Assemble the complete one-frame count-sixteen finite catalogue by
inserting the generated primitive row-three pilot. -/
noncomputable def sixteenOneFrameFiniteCatalogue
    (D : RemainingPairTopSemanticData) :
    SixteenOneFrameCatalogue.DegreeTwoSixteenOneFrameFiniteCatalogueData :=
  SixteenOneFrameCatalogue.ofGeneratedPrimitiveRow3
    SixteenPilot.finiteData D.sixteenOneFrame

/-- Count-sixteen resolution with every paired-eight and one-frame row
supplied by finite certificates. -/
noncomputable def sixteenResolution
    (D : RemainingPairTopSemanticData)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) :
    DegreeTwoSixteenPairTopCatalogueResolution SixteenCatalogue where
  paired8 j p realization := by
    exact (((PairedEightFinite.ofGeneratedRow1 D.sixteenPaired8).
      rowData hZmud j realization).sixteenResolvedData lit).toResolvedRow
  zero16 j p realization :=
    (D.sixteenOneFrameFiniteCatalogue.zero16ResolvedRow
      hZmud lit j realization)
  twoAffine16 j p realization :=
    (D.sixteenOneFrameFiniteCatalogue.twoAffine16ResolvedRow
      hZmud lit j realization)
  primitive16 j p realization :=
    (D.sixteenOneFrameFiniteCatalogue.primitive16ResolvedRow
      hZmud lit j realization)
  natural kind p realization :=
    D.sixteenNatural.source hZmud lit kind p realization

end RemainingPairTopSemanticData

/-- Degree-two residual source with every count-twelve and count-sixteen
row routed through an explicit finite package and a family-level generic
converter. -/
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
