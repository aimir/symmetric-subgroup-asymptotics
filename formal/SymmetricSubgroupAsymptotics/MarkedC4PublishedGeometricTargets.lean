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
import SymmetricSubgroupAsymptotics.CharacterLiteratureProvedBinary
import SymmetricSubgroupAsymptotics.RDTDegreeEightExceptionalProof
import SymmetricSubgroupAsymptotics.MarkedC4SubquadraticContainersGlobal
import SymmetricSubgroupAsymptotics.T1CatalogueFromMarkedMoment
import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequencesFinal
import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterProof
import SymmetricSubgroupAsymptotics.RDTBoundedFactorEpimorphismProof
import SymmetricSubgroupAsymptotics.SmallAffineCatalogueDegreeEightConsequences

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
primitive structure, bounded catalogue, and soluble linear cube bound.
The binary abelian-quotient theorem and the degree-eight binary exception
are proved internally. The container menu uses the retained subquadratic
transitive count; the stronger Pyber representative estimate is unnecessary.
The large-orbit soluble generator theorem is derived from the retained
primitive normal-generator, composition-length and refined Tracey inputs.
The arbitrary-normal-target bounded-factor epimorphism theorem is proved
from joint kernel incidence and short adapted original generating tuples.
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
    (hseven : PublishedTheoremSeven)
    (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (compositionCatalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (strictCatalogue : PublishedPrimitiveStrictHeadCatalogueCorrespondence)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (smallAffineCatalogue : SmallAffineCatalogueDegreeEightConsequences.PublishedRemainingClassification)
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
  let fullLit := lit.toLiterature
  have hZmud := zmudFaithfulCharacterTupleInput_proved
  have rdt46 := RDTBoundedFactorEpimorphismProof.rdtTheorem46BinaryInput_proved
  have hsub := publishedSolubleSubdirectHeight
  have publishedSix :=
    DegreeSixThreeByTwoClassificationProof.publishedDegreeSixThreeByTwoAffineClassification
  have publishedThree := DegreeSixThreePairClassificationProof.representativeClassification
  have hDixon := SolublePermutationOrderProof.dixonOrder_of_primitive_inputs
    compositionCatalogue hONanScott hSolubleBase
  have h8 := RDTDegreeEightExceptionalProof.publishedDegreeEightExceptional
  have h62 := LargeOrbitGeneratorConsequences.publishedProposition62_of_retained_inputs
    hPrimitiveGen hTraceyRefined hcomp
  have hM4 := SubquadraticContainersGlobal.marked_bound hsub hseven
    fullLit.kovacsPraeger fullLit.kovacsPraegerBinary h55 h53 h57 h8 hderived
    rdt46 hodd h62 hLMM hDixon hAG
  exact T1_of_globalMarkedMoment_and_catalogues fullLit hM4 hZmud hcomp hodd
    hExceptionalOrbits compositionCatalogue hPrimitiveGen strictCatalogue hLMM
    hTraceyRefined hTraceyPerm hSimpleGen
    (PublishedPrimitiveAffineFiniteLiterature.ofCanonicalClassifications
      (SmallAffineCatalogueDegreeEightConsequences.published_of_remaining smallAffineCatalogue)
      ProjectiveThreeSimplicity.proved burnsideTwoPrimeSolvability
      PGLTwoFiveIsomorphism.publishedProjectiveIsomorphism hSolubleBase
      DegreeFiveAffineClassification.classification)
    (hONanScott.toSocleDichotomy hSimpleIndex) catalogue hTraceySoluble hMN
    publishedSix published8 published16 publishedThree publishedTwelve

/-- The same published inputs imply all three approved asymptotic targets. -/
theorem allTargets_of_published_inputs
    (lit : PreE7CharacterPublishedInputs)
    (hcomp : PrimitiveCompositionLengthInput)
    (hseven : PublishedTheoremSeven)
    (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (compositionCatalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (strictCatalogue : PublishedPrimitiveStrictHeadCatalogueCorrespondence)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (smallAffineCatalogue : SmallAffineCatalogueDegreeEightConsequences.PublishedRemainingClassification)
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
    lit hcomp hseven h55 h53 h57 hderived
    hodd hAG hExceptionalOrbits compositionCatalogue
    hPrimitiveGen strictCatalogue hLMM
    hTraceyRefined hTraceyPerm
    hSimpleGen smallAffineCatalogue hSolubleBase
    hONanScott hSimpleIndex catalogue hTraceySoluble hMN
    published8 published16 publishedTwelve)


end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
