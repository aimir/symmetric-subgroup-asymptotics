import SymmetricSubgroupAsymptotics.MarkedC4PublishedClosedTargets
import SymmetricSubgroupAsymptotics.DegreeSixteenCompleteGeometricSource
import SymmetricSubgroupAsymptotics.CliffordActualRetainedConstituent
import SymmetricSubgroupAsymptotics.TraceyExceptionalThreeFromRaw
import SymmetricSubgroupAsymptotics.PrimitiveAffineCanonicalFiniteLiterature
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawDichotomy
import SymmetricSubgroupAsymptotics.PermutationGeneratorBoundFromMcIverNeumann
import SymmetricSubgroupAsymptotics.BurnsideTwoPrimeSolvability
import SymmetricSubgroupAsymptotics.CliffordRestriction
import SymmetricSubgroupAsymptotics.BinaryNormalSubgroupBound
import SymmetricSubgroupAsymptotics.ProjectiveThreeSimplicity
import SymmetricSubgroupAsymptotics.TraceyRefinedInputConsequences
import SymmetricSubgroupAsymptotics.FaithfulSimpleGeneratorFromTwoGeneration
import SymmetricSubgroupAsymptotics.PGLTwoFiveIsomorphism
import SymmetricSubgroupAsymptotics.DegreeFiveAffineClassificationComplete
import SymmetricSubgroupAsymptotics.PrimitiveDegreeNineFromCompositionCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixCatalogueClassification
import SymmetricSubgroupAsymptotics.TraceyPermutationFormulaConsequences
import SymmetricSubgroupAsymptotics.TraceySolublePermutationConsequences
import SymmetricSubgroupAsymptotics.SolublePermutationOrderBound
import SymmetricSubgroupAsymptotics.SolubleSubdirectSocleHeight
import SymmetricSubgroupAsymptotics.DegreeSixThreePairClassificationProof
import SymmetricSubgroupAsymptotics.DegreeSixThreeByTwoClassificationProof

/-! Target composition from the explicit current mathematical inputs.
Every low-degree source and the degree-sixteen geometric cover is assembled
internally. The exceptional Tracey head and the actual retained Clifford
corollary, the full 34-row affine receipt, and the degree-25 projective
composition consequence, and the quantitative nonaffine socle profile are
constructed internally from raw published inputs. The rounded generator
bound is derived from the existing McIver--Neumann input. The incomplete sixteen-point locator is not used. The final
source/dependency and literature-boundary audit is separate from proving
this composition. The degree-six/nine slices and binary/soluble permutation
Tracey formulae are derived from the stronger retained inputs. The standalone
Kovács--Praeger input is supplied by the character literature bundle.
Soluble subdirect socle height and both degree-six block classifiers are
proved internally. Dixon's order estimate is derived from the retained
primitive structure, bounded catalogue, and soluble linear cube bound.
See formal/README.md. -/
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
    (hcomp : PrimitiveCompositionLengthInput)
    (hseven : PublishedTheoremSeven)
    (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (rdt46 : RDTTheorem46BinaryInput)
    (hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (h62 : PublishedProposition62) (h86 : PublishedTheorem86Representatives)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (compositionCatalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (strictCatalogue : PublishedPrimitiveStrictHeadCatalogueCorrespondence)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (smallAffineCatalogue : SmallAffineCanonicalRepresentatives.PublishedClassification)
    (hSolubleBase : HalasiMarotiSolubleIrreducibleCubeBound)
    (hONanScott : PrimitiveSocleRawStructure.PublishedONanScottStructure)
    (hSimpleIndex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (hTraceySoluble : TraceySolubleOrbitInducedModuleInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (publishedTwelve : DegreeTwelveCanonicalCatalogueLocator.PublishedClassification)
    : T1 := by
  have hsub := publishedSolubleSubdirectHeight
  have publishedSix :=
    DegreeSixThreeByTwoClassificationProof.publishedDegreeSixThreeByTwoAffineClassification
  have publishedThree := DegreeSixThreePairClassificationProof.representativeClassification
  have hDixon := SolublePermutationOrderProof.dixonOrder_of_primitive_inputs
    compositionCatalogue hONanScott hSolubleBase
  have hKP := lit.kovacsPraeger
  have hSolubleFormula := hTraceySoluble.permutationFormulaRaw
  have primitiveSix :=
    PrimitiveDegreeSixCatalogueClassification.publishedPrimitiveDegreeSixClassification_of_compositionCatalogue
      compositionCatalogue
  have hTracey := hTraceyRefined.binaryFormula
  have hDegreeNine := primitiveDegreeNineClassification_of_compositionCatalogue compositionCatalogue
  have hHoltRoneyDougal := hSimpleGen.faithfulSimplePermutationGeneratorBound
  have hTraceyHalf := hTraceyRefined.affineHalf
  have hTraceyLog := hTraceyRefined.affine
  let socle := hONanScott.toSocleDichotomy hSimpleIndex
  have hgen := permutationSubgroupGeneratorBound_of_mcIverNeumann hMN
  exact T1_of_published_inputs_and_sixteenPairSource
    lit hZmud CliffordRawRestriction.proved.toHomogeneousRestriction hgen hcomp hsub hseven h55 h53 h57 h8 hderived
    rdt46 hodd h62 h86 hDixon hAG hTracey
    (traceyBinaryExceptionalThree_of_raw hSolubleFormula hExceptionalOrbits) compositionCatalogue
    hDegreeNine hPrimitiveGen strictCatalogue primitiveSix hKP hLMM
    hHoltRoneyDougal hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    hSimpleGen
    (PublishedPrimitiveAffineFiniteLiterature.ofCanonicalClassifications
      smallAffineCatalogue ProjectiveThreeSimplicity.proved burnsideTwoPrimeSolvability
      PGLTwoFiveIsomorphism.publishedProjectiveIsomorphism hSolubleBase
      DegreeFiveAffineClassification.classification)
    socle catalogue hTraceySoluble hMN
    publishedSix published8 published16 publishedThree publishedTwelve
    (DegreeSixteenCompleteGeometricSource.residualSource
      published8 published16 socle hMN hZmud lit) fusariSpigaBinaryNormalSubgroup

/-- The same published inputs imply all three approved asymptotic targets. -/
theorem allTargets_of_published_inputs
    (lit : PreE7CharacterLiterature)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hcomp : PrimitiveCompositionLengthInput)
    (hseven : PublishedTheoremSeven)
    (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (rdt46 : RDTTheorem46BinaryInput)
    (hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (h62 : PublishedProposition62) (h86 : PublishedTheorem86Representatives)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (compositionCatalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (strictCatalogue : PublishedPrimitiveStrictHeadCatalogueCorrespondence)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (smallAffineCatalogue : SmallAffineCanonicalRepresentatives.PublishedClassification)
    (hSolubleBase : HalasiMarotiSolubleIrreducibleCubeBound)
    (hONanScott : PrimitiveSocleRawStructure.PublishedONanScottStructure)
    (hSimpleIndex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (hTraceySoluble : TraceySolubleOrbitInducedModuleInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (publishedTwelve : DegreeTwelveCanonicalCatalogueLocator.PublishedClassification)
    : AllTargets := by
  exact allTargets_iff_T1.mpr (T1_of_published_inputs
    lit hZmud hcomp hseven h55 h53 h57 h8 hderived
    rdt46 hodd h62 h86 hAG hExceptionalOrbits compositionCatalogue
    hPrimitiveGen strictCatalogue hLMM
    hTraceyRefined hTraceyPerm
    hSimpleGen smallAffineCatalogue hSolubleBase
    hONanScott hSimpleIndex catalogue hTraceySoluble hMN
    published8 published16 publishedTwelve)


end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
