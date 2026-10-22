import SymmetricSubgroupAsymptotics.CFSGSolubleOrbitFinal
import SymmetricSubgroupAsymptotics.BinaryAffineSmallCatalogueConstruction
import SymmetricSubgroupAsymptotics.PrimitiveAffineFiniteInputFromBinaryCatalogue
import SymmetricSubgroupAsymptotics.TraceyRefinedInducedModuleProof
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
import SymmetricSubgroupAsymptotics.ElementaryDixonOrderBound
import SymmetricSubgroupAsymptotics.SolubleSubdirectSocleHeight
import SymmetricSubgroupAsymptotics.DegreeSixThreePairClassificationProof
import SymmetricSubgroupAsymptotics.DegreeSixThreeByTwoClassificationProof
import SymmetricSubgroupAsymptotics.CharacterLiteratureProvedBinary
import SymmetricSubgroupAsymptotics.RDTDegreeEightExceptionalProof
import SymmetricSubgroupAsymptotics.BoundedCoreSubquadraticContainersGlobal
import SymmetricSubgroupAsymptotics.CFSGConstructedContainersGlobal
import SymmetricSubgroupAsymptotics.T1CatalogueFromFinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightyOneFromComposition
import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequencesFinal
import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterProof
import SymmetricSubgroupAsymptotics.RDTBoundedFactorEpimorphismProof
import SymmetricSubgroupAsymptotics.SmallAffineCatalogueDegreeEightConsequences
import SymmetricSubgroupAsymptotics.BinaryDerivedNormalQuarterProof
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof
import SymmetricSubgroupAsymptotics.BinaryOriginalWordConsequences
import SymmetricSubgroupAsymptotics.S8TransitiveCanonicalCoverage

import SymmetricSubgroupAsymptotics.PrimitiveAffineFiniteInputFromGenericTwentySeven
import SymmetricSubgroupAsymptotics.ElementaryDixonOrderWithoutCatalogue
import SymmetricSubgroupAsymptotics.T1FromActualPrimitiveAndTwelveConsumers

/-! Actual primitive consumers replace the stronger unused bounded composition
correspondence. The actual12-point pair source uses its literal top as comparator;
this endpoint retains exactly the other published inputs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer
open MarkedC4 MarkedC4.RDTOriginalWordStructure MarkedC4.RDTNormalFInterface
open MarkedC4.OrdinaryNilpotentGeneration MarkedC4.LargeOrbitOrdinaryGeneration
open MarkedC4.SolubleContainerCount MarkedC4.SolubleContainerOrder

theorem T1_of_published_inputs_actualConsumers
    (lit : PreE7CharacterPublishedInputs)
    (hcomp : PrimitiveCompositionLengthInput)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (hSimpleIndex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    : T1 := by
  have published8 := S8TransitiveCanonicalCoverage.publishedClassification
  let fullLit := lit.toLiterature
  have hTraceyRefined := traceyRefinedInducedModuleInput_proved
  have hZmud := zmudFaithfulCharacterTupleInput_proved
  have rdt46 := RDTBoundedFactorEpimorphismProof.rdtTheorem46BinaryInput_proved
  have hderived := publishedDerivedNormalQuarterBinary_proved
  have hONanScott := PrimitiveSocleRawStructure.publishedONanScottStructure
  have h55 := publishedTheorem55Binary_of_proposition53 h53
  have publishedSix :=
    DegreeSixThreeByTwoClassificationProof.publishedDegreeSixThreeByTwoAffineClassification
  have publishedThree := DegreeSixThreePairClassificationProof.representativeClassification
  let publishedSmall := BinaryAffineSmallCatalogueData.ofPrimitiveSixteen published16
  let publishedFinite := publishedPrimitiveAffineFiniteInput_of_binary_and_genericTwentySeven
    publishedSmall
    (DegreeTwentyFiveActualProjectiveData.publishedDegreeTwentyFiveLinearData
      burnsideTwoPrimeSolvability PGLTwoFiveIsomorphism.publishedProjectiveIsomorphism)
    (primitiveAffineEightyOne_complement_le_cube hcomp)
    (degreeFiveSource_of_publishedClassification DegreeFiveAffineClassification.classification)
  have h8 := RDTDegreeEightExceptionalProof.publishedDegreeEightExceptional
  have h62 := CFSGSolubleOrbitConsequences.publishedProposition62_proved
  have hM4 := CFSGConstructedContainersGlobal.marked_bound
    fullLit.kovacsPraeger fullLit.kovacsPraegerBinary h55 h53 h57 h8 hderived
    rdt46 hodd h62 hAG
  exact T1_of_globalMarkedMoment_actualPrimitiveAndTwelveConsumers fullLit hM4 hZmud hcomp hodd
    hExceptionalOrbits hPrimitiveGen hSimpleIndex hLMM
    hTraceyRefined hTraceyPerm hSimpleGen
    publishedSmall publishedFinite
    (hONanScott.toSocleDichotomy hSimpleIndex) hMN
    publishedSix published8 published16 publishedThree

/-- The same published inputs imply all three approved asymptotic targets. -/
theorem allTargets_of_published_inputs_actualConsumers
    (lit : PreE7CharacterPublishedInputs)
    (hcomp : PrimitiveCompositionLengthInput)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (hSimpleIndex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    : AllTargets := by
  exact allTargets_iff_T1.mpr (T1_of_published_inputs_actualConsumers
    lit hcomp h53 h57
    hodd hAG hExceptionalOrbits
    hPrimitiveGen hLMM
    hTraceyPerm
    hSimpleGen
    hSimpleIndex hMN
    published16)


end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
