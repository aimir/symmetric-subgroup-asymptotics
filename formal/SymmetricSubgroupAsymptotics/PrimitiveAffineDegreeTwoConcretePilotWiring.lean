import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoConcreteResidualAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveInstalledJoint
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveInstalledCores
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedSixOriginalQuotients
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenInstalledSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenNaturalSymbolicCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightCompleteCatalogue

/-!
# Concrete pilot wiring in the degree-two residual source

The paired-eight catalogue and the natural `A_16`/`S_16` alternatives are
supplied by their proved packages. All sixty-four one-frame natural-module
bounds and the installed original quotient-socle families are also supplied
internally, as are all eight core and both paired-six original-quotient
certificates. The remaining fields request only genuinely unfinished data.

The exceptional twelve-point branch retains a certificate on each actual
original quotient. It no longer requests the obsolete scalar top-socle
bound. This is a conditional assembler, not a proof of its remaining fields.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoConcretePilotWiring


abbrev TwelveCatalogue := DegreeTwoConcreteResidualAssembly.TwelveCatalogue
abbrev SixteenCatalogue := DegreeTwoConcreteResidualAssembly.SixteenCatalogue

/-- Unfinished original-top data. No field accepts a final counting source,
and completed paired-eight, natural-module or natural-top bounds are not
requested again. -/
structure RemainingPairTopSemanticData : Type 1 where
  twelveJoint :
    DegreeTwoTwelveInstalledJoint.RemainingData
  sixteenOneFrame :
    DegreeTwoSixteenInstalledSocles.RemainingData

namespace RemainingPairTopSemanticData

/-- Count-twelve resolution with all 283 joint rows supplied by the generic
finite Schur package.  The completed whole packages and natural-module fields are inserted
before catalogue dispatch. -/
noncomputable def twelveResolution
    (D : RemainingPairTopSemanticData)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) :
    DegreeTwoTwelvePairTopCatalogueResolution TwelveCatalogue := by
  let jointFinite :
      DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteCatalogueData
        TwelveCatalogue :=
    D.twelveJoint.finiteCatalogue
  intro j p realization
  cases hbranch : (TwelveCatalogue.row j).branch with
  | joint =>
    exact jointFinite.resolvedRow hZmud lit
      (fun i hi ↦ DegreeTwoTwelvePairFiniteCatalogue.joint_parameters i hi)
      j realization hbranch
  | core =>
    exact DegreeTwoTwelvePairedSixOriginalQuotients.exceptionalCatalogueData.coreResolvedRow
      hZmud lit j realization hbranch
  | ternary =>
    exact (degreeTwoFourTernaryCatalogueCompression
      PrimitiveAffineDegreeTwoFourTernaryAffineWitnesses.compressionPackages
      j p realization hbranch).resolvedRow hZmud lit
  | paired =>
    exact DegreeTwoTwelvePairedSixOriginalQuotients.exceptionalCatalogueData.pairedResolvedRow
      hZmud lit j realization hbranch

/-- Supply the proved natural-module and installed quotient-socle bounds. -/
noncomputable def sixteenOneFrameFiniteCatalogue
    (D : RemainingPairTopSemanticData) :
    DegreeTwoSixteenOneFrameFiniteRows.Catalogue.DegreeTwoSixteenOneFrameFiniteCatalogueData :=
  D.sixteenOneFrame.finiteCatalogue

/-- Count-sixteen resolution with every paired-eight and one-frame row
supplied by finite certificates. -/
noncomputable def sixteenResolution
    (D : RemainingPairTopSemanticData)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) :
    DegreeTwoSixteenPairTopCatalogueResolution SixteenCatalogue where
  paired8 j p realization := by
    exact DegreeTwoPairedEightCompleteCatalogue.resolvedRow hZmud lit j realization
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
    DegreeTwoSixteenNaturalFiniteRows.symbolicCatalogue.source hZmud lit kind p realization

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
    (publishedTwelve : DegreeTwoConcreteResidualAssembly.PublishedTwelveCatalogueLocator)
    (publishedSixteen : DegreeTwoConcreteResidualAssembly.PublishedSixteenCatalogueLocator)
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
