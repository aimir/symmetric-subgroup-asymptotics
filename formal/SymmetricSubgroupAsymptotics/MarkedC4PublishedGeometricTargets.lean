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
import SymmetricSubgroupAsymptotics.T1CatalogueFromFinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightyOneFromComposition
import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequencesFinal
import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterProof
import SymmetricSubgroupAsymptotics.RDTBoundedFactorEpimorphismProof
import SymmetricSubgroupAsymptotics.SmallAffineCatalogueDegreeEightConsequences
import SymmetricSubgroupAsymptotics.BinaryDerivedNormalQuarterProof
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof
import SymmetricSubgroupAsymptotics.BinaryOriginalWordConsequences

/-! Target composition from the explicit current mathematical inputs.
The degree-eight small-affine complement classification is proved from
complete checked GL(3,2) subgroup coverage; only degrees sixteen and
twenty-seven remain in the small-affine classification parameter.
Every low-degree source and the degree-sixteen geometric cover is assembled
internally. The exceptional Tracey head and the actual retained Clifford
corollary, the full 34-row affine receipt, and the degree-25 projective
composition consequence, and the quantitative nonaffine socle profile are
constructed internally from raw published inputs. The rounded generator
bound is derived from the existing McIver--Neumann input. The incomplete sixteen-point locator is not used. The final
source/dependency and literature-boundary audit is separate from proving
this composition. The degree-six/nine slices and binary/soluble permutation
Tracey formulae are derived from the stronger retained inputs. The full Kovács--Praeger and faithful-character tuple theorems are proved
internally; the character bundle retains only the general permutation class-number field. The nilpotent class-number
bound is proved through prime-group fourth-power estimates and actual coprime
support compression.
Soluble subdirect socle height and both degree-six block classifiers are
proved internally. Dixon's order estimate is derived from the retained
bounded catalogue and elementary affine counting, using the proved raw
O'Nan--Scott structure of the actual full socle.
The binary abelian-quotient theorem and the degree-eight binary exception
are proved internally. The container menu uses the retained subquadratic
transitive count; the stronger Pyber representative estimate is unnecessary.
The large-orbit soluble generator theorem is derived from the retained
primitive normal-generator, composition-length and refined Tracey inputs.
The arbitrary-normal-target bounded-factor epimorphism theorem is proved
from joint kernel incidence and short adapted original generating tuples.
The derived-normal quarter bound is proved by original pair-kernel degree
induction, independently of the excess classification.
The original-word theorem follows internally from the retained exact excess
classification and the proved proper-normal ceiling.
The bounded-orbit nilpotent-core construction supplies the marked moment
without the sharper unrestricted Theorem Seven input.
The degree-81 finite complement budget follows from the retained composition
length theorem; elementary affine counting supplies Dixon without a linear-base input.
See formal/README.md. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer
open MarkedC4 MarkedC4.RDTOriginalWordStructure MarkedC4.RDTNormalFInterface
open MarkedC4.OrdinaryNilpotentGeneration MarkedC4.LargeOrbitOrdinaryGeneration
open MarkedC4.SolubleContainerCount MarkedC4.SolubleContainerOrder

theorem T1_of_published_inputs
    (lit : PreE7CharacterPublishedInputs)
    (hcomp : PrimitiveCompositionLengthInput)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (compositionCatalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (strictCatalogue : PublishedPrimitiveStrictHeadCatalogueCorrespondence)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (smallAffineCatalogue : SmallAffineCatalogueDegreeEightConsequences.PublishedRemainingClassification)
    (hSimpleIndex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (publishedTwelve : DegreeTwelveCanonicalCatalogueLocator.PublishedClassification)
    : T1 := by
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
  have hDixon := ElementaryDixonOrderProof.dixonOrder_of_primitive_inputs
    compositionCatalogue hONanScott
  let smallClassification : SmallAffineCanonicalRepresentatives.PublishedClassification :=
    SmallAffineCatalogueDegreeEightConsequences.published_of_remaining smallAffineCatalogue
  let publishedSmall : PublishedPrimitiveAffineSmallCatalogueData := {
    locator := SmallAffineCanonicalRepresentatives.locator smallClassification
    representativeFacts := SmallAffineCanonicalRepresentatives.receipt
      smallClassification ProjectiveThreeSimplicity.proved burnsideTwoPrimeSolvability }
  let publishedFinite := publishedPrimitiveAffineFiniteInput_of_structural publishedSmall
    (DegreeTwentyFiveActualProjectiveData.publishedDegreeTwentyFiveLinearData
      burnsideTwoPrimeSolvability PGLTwoFiveIsomorphism.publishedProjectiveIsomorphism)
    (primitiveAffineEightyOne_complement_le_cube hcomp)
    (degreeFiveSource_of_publishedClassification DegreeFiveAffineClassification.classification)
  have h8 := RDTDegreeEightExceptionalProof.publishedDegreeEightExceptional
  have h62 := LargeOrbitGeneratorConsequences.publishedProposition62_of_retained_inputs
    hPrimitiveGen hTraceyRefined hcomp
  have hM4 := BoundedCoreSubquadraticContainersGlobal.marked_bound
    fullLit.kovacsPraeger fullLit.kovacsPraegerBinary h55 h53 h57 h8 hderived
    rdt46 hodd h62 hLMM hDixon hAG
  exact T1_of_globalMarkedMoment_and_finitePackage fullLit hM4 hZmud hcomp hodd
    hExceptionalOrbits compositionCatalogue hPrimitiveGen strictCatalogue hLMM
    hTraceyRefined hTraceyPerm hSimpleGen
    publishedSmall publishedFinite
    (hONanScott.toSocleDichotomy hSimpleIndex) catalogue hMN
    publishedSix published8 published16 publishedThree publishedTwelve

/-- The same published inputs imply all three approved asymptotic targets. -/
theorem allTargets_of_published_inputs
    (lit : PreE7CharacterPublishedInputs)
    (hcomp : PrimitiveCompositionLengthInput)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (compositionCatalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (strictCatalogue : PublishedPrimitiveStrictHeadCatalogueCorrespondence)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (smallAffineCatalogue : SmallAffineCatalogueDegreeEightConsequences.PublishedRemainingClassification)
    (hSimpleIndex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (publishedTwelve : DegreeTwelveCanonicalCatalogueLocator.PublishedClassification)
    : AllTargets := by
  exact allTargets_iff_T1.mpr (T1_of_published_inputs
    lit hcomp h53 h57
    hodd hAG hExceptionalOrbits compositionCatalogue
    hPrimitiveGen strictCatalogue hLMM
    hTraceyPerm
    hSimpleGen smallAffineCatalogue
    hSimpleIndex catalogue hMN
    published8 published16 publishedTwelve)


end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
