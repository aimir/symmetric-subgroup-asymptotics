import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoConcreteResidualAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow1Resolution
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveExceptionalTemplates
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow3Resolution
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightCoupledCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopRelativeKernelOrbitRows

/-!
# Concrete pilot wiring in the degree-two residual source

Every joint count-twelve row, every paired-eight row, and every zero16,
twoAffine16, and primitive16 row is routed through concrete finite
certificates.  The 283 joint count-twelve rows use quotient-socle and
natural-module declarations; the paired-eight rows use their three finite
declarations; and all 64 one-frame count-sixteen rows share the finite
`(2,4)` Schur package.

The only remaining count-sixteen semantic boundary is the natural
`A_16`/`S_16` alternative.
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

abbrev TwelveCatalogue := Concrete.TwelveCatalogue
abbrev SixteenCatalogue := Concrete.SixteenCatalogue

/-- Semantic and finite data for the rows not already generated.  Joint
count-twelve, paired-eight, and all one-frame count-sixteen rows accept only
finite declarations on their literal tops.  Their explicit family fields
are the boundaries consumed by the serialized certificate exporters. -/
structure RemainingPairTopSemanticData : Type 1 where
  twelveJoint :
    TwelveJointCatalogue.RemainingDegreeTwoTwelveJointFiniteRowData
  twelveExceptional :
    TwelveExceptional.DegreeTwoTwelveExceptionalCatalogueData
  sixteenPaired8 :
    RemainingDegreeTwoPairedEightFiniteRowData
  sixteenOneFrame :
    SixteenOneFrameCatalogue.RemainingDegreeTwoSixteenOneFrameFiniteRowData
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
  cases hbranch : (TwelveCatalogue.row j).branch with
  | joint =>
    exact jointFinite.resolvedRow hZmud lit
      (fun i hi ↦ TwelveFiniteCatalogue.joint_parameters i hi)
      j realization hbranch
  | core =>
    exact D.twelveExceptional.coreResolvedRow lit j realization hbranch
  | ternary =>
    exact D.twelveExceptional.ternaryResolvedRow j realization hbranch
  | paired =>
    exact D.twelveExceptional.pairedResolvedRow lit j realization hbranch

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
    (D.sixteenNatural kind p realization).source hZmud lit

end RemainingPairTopSemanticData

/-- Degree-two residual source with the checked catalogue pilots and the
uniform joint-twelve, paired-eight, and one-frame count-sixteen finite
dispatch installed at their literal indices. -/
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
