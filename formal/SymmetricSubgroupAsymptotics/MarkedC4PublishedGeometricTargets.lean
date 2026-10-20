import SymmetricSubgroupAsymptotics.MarkedC4PublishedClosedTargets
import SymmetricSubgroupAsymptotics.DegreeSixteenCompleteGeometricSource
import SymmetricSubgroupAsymptotics.CliffordActualRetainedConstituent
import SymmetricSubgroupAsymptotics.TraceyExceptionalThreeFromRaw
import SymmetricSubgroupAsymptotics.PrimitiveAffineCanonicalFiniteLiterature
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawDichotomy
import SymmetricSubgroupAsymptotics.PermutationGeneratorBoundFromMcIverNeumann

/-! Target composition from the explicit current mathematical inputs.
Every low-degree source and the degree-sixteen geometric cover is assembled
internally. The exceptional Tracey head and the actual retained Clifford
corollary, the full 34-row affine receipt, and the degree-25 projective
composition consequence, and the quantitative nonaffine socle profile are
constructed internally from raw published inputs. The rounded generator
bound is derived from the existing McIver--Neumann input. The incomplete sixteen-point locator is not used. The final
source/dependency and literature-boundary audit is separate from proving
this composition. See formal/README.md. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer
open MarkedC4 MarkedC4.RDTOriginalWordStructure MarkedC4.RDTNormalFInterface
open MarkedC4.OrdinaryNilpotentGeneration MarkedC4.LargeOrbitOrdinaryGeneration
open MarkedC4.SolubleContainerCount MarkedC4.SolubleContainerOrder

theorem T1_of_published_inputs
    (lit : PreE7CharacterLiterature)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hClifford : CliffordRawRestriction.Input)
    (hcomp : PrimitiveCompositionLengthInput)
    (hsub : PublishedSolubleSubdirectHeight) (hseven : PublishedTheoremSeven)
    (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (rdt46 : RDTTheorem46BinaryInput)
    (hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (h62 : PublishedProposition62) (h86 : PublishedTheorem86Representatives)
    (hDixon : PublishedDixonOrder)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hTracey : TraceyBinaryFormulaInput)
    (hSolubleFormula : TraceySolublePermutationFormulaRawInput)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (compositionCatalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hDegreeNine : PublishedPrimitiveDegreeNineClassification)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (strictCatalogue : PublishedPrimitiveStrictHeadCatalogueCorrespondence)
    (primitiveSix : PublishedPrimitiveDegreeSixClassification)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hHoltRoneyDougal : FaithfulSimplePermutationGeneratorBound)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (smallAffineCatalogue : SmallAffineCanonicalRepresentatives.PublishedClassification)
    (hPSLThree : StandardThreeDimensionalLinearGroups.PublishedSimplicity)
    (hBurnside : PublishedBurnsideTwoPrimeSolvabilityInput)
    (hProjectiveFive : StandardGLTwoFiveProjective.PublishedProjectiveIsomorphism)
    (hSolubleBase : HalasiMarotiSolubleIrreducibleCubeBound)
    (hAffineFive : PublishedDegreeFiveAffineClassification)
    (hONanScott : PrimitiveSocleRawStructure.PublishedONanScottStructure)
    (hSimpleIndex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (hTraceySoluble : TraceySolubleOrbitInducedModuleInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (publishedTwelve : DegreeTwelveCanonicalCatalogueLocator.PublishedClassification)
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : T1 := by
  let socle := hONanScott.toSocleDichotomy hSimpleIndex
  have hgen := permutationSubgroupGeneratorBound_of_mcIverNeumann hMN
  exact T1_of_published_inputs_and_sixteenPairSource
    lit hZmud hClifford.toHomogeneousRestriction hgen hcomp hsub hseven h55 h53 h57 h8 hderived
    rdt46 hodd h62 h86 hDixon hAG hTracey
    (traceyBinaryExceptionalThree_of_raw hSolubleFormula hExceptionalOrbits) compositionCatalogue
    hDegreeNine hPrimitiveGen strictCatalogue primitiveSix hKP hLMM
    hHoltRoneyDougal hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    hSimpleGen
    (PublishedPrimitiveAffineFiniteLiterature.ofCanonicalClassifications
      smallAffineCatalogue hPSLThree hBurnside hProjectiveFive hSolubleBase hAffineFive)
    socle catalogue hTraceySoluble hMN
    publishedSix published8 published16 publishedThree publishedTwelve
    (DegreeSixteenCompleteGeometricSource.residualSource
      published8 published16 socle hMN hZmud lit) hFS

/-- The same published inputs imply all three approved asymptotic targets. -/
theorem allTargets_of_published_inputs
    (lit : PreE7CharacterLiterature)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hClifford : CliffordRawRestriction.Input)
    (hcomp : PrimitiveCompositionLengthInput)
    (hsub : PublishedSolubleSubdirectHeight) (hseven : PublishedTheoremSeven)
    (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (rdt46 : RDTTheorem46BinaryInput)
    (hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (h62 : PublishedProposition62) (h86 : PublishedTheorem86Representatives)
    (hDixon : PublishedDixonOrder)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hTracey : TraceyBinaryFormulaInput)
    (hSolubleFormula : TraceySolublePermutationFormulaRawInput)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (compositionCatalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hDegreeNine : PublishedPrimitiveDegreeNineClassification)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (strictCatalogue : PublishedPrimitiveStrictHeadCatalogueCorrespondence)
    (primitiveSix : PublishedPrimitiveDegreeSixClassification)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hHoltRoneyDougal : FaithfulSimplePermutationGeneratorBound)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (smallAffineCatalogue : SmallAffineCanonicalRepresentatives.PublishedClassification)
    (hPSLThree : StandardThreeDimensionalLinearGroups.PublishedSimplicity)
    (hBurnside : PublishedBurnsideTwoPrimeSolvabilityInput)
    (hProjectiveFive : StandardGLTwoFiveProjective.PublishedProjectiveIsomorphism)
    (hSolubleBase : HalasiMarotiSolubleIrreducibleCubeBound)
    (hAffineFive : PublishedDegreeFiveAffineClassification)
    (hONanScott : PrimitiveSocleRawStructure.PublishedONanScottStructure)
    (hSimpleIndex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (hTraceySoluble : TraceySolubleOrbitInducedModuleInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (publishedTwelve : DegreeTwelveCanonicalCatalogueLocator.PublishedClassification)
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : AllTargets := by
  exact allTargets_iff_T1.mpr (T1_of_published_inputs
    lit hZmud hClifford hcomp hsub hseven h55 h53 h57 h8 hderived
    rdt46 hodd h62 h86 hDixon hAG hTracey hSolubleFormula hExceptionalOrbits compositionCatalogue
    hDegreeNine hPrimitiveGen strictCatalogue primitiveSix hKP hLMM
    hHoltRoneyDougal hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    hSimpleGen smallAffineCatalogue hPSLThree hBurnside hProjectiveFive hSolubleBase hAffineFive
    hONanScott hSimpleIndex catalogue hTraceySoluble hMN
    publishedSix published8 published16 publishedThree publishedTwelve hFS)


end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
