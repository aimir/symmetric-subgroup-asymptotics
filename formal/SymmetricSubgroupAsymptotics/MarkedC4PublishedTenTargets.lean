import SymmetricSubgroupAsymptotics.MarkedC4PublishedGeometricTargets
import SymmetricSubgroupAsymptotics.CFSGOrdinarySubgroupUpperFromSoluble

/-! Public targets with ten independent published inputs. The coarse
ordinary subgroup count is supplied internally from the retained soluble
generation input, using unconditional soluble primitive and large-orbit bounds.
No CFSG family hypothesis is hidden in this reduction. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4
open MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_ten_published_inputs
    (lit : PreE7CharacterPublishedInputs)
    (hcomp : PrimitiveCompositionLengthInput)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (hSimpleIndex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (hMN : McIverNeumannPermutationGeneratorBound) : T1 := by
  exact T1_of_published_inputs lit hcomp
    (CFSGReduction.ordinarySubgroupUpper_of_soluble_generation hAG)
    hAG hExceptionalOrbits hPrimitiveGen hLMM hTraceyPerm hSimpleGen hSimpleIndex hMN

theorem allTargets_of_ten_published_inputs
    (lit : PreE7CharacterPublishedInputs)
    (hcomp : PrimitiveCompositionLengthInput)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (hSimpleIndex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (hMN : McIverNeumannPermutationGeneratorBound) : AllTargets := by
  exact allTargets_iff_T1.mpr (T1_of_ten_published_inputs lit hcomp hAG
    hExceptionalOrbits hPrimitiveGen hLMM hTraceyPerm hSimpleGen hSimpleIndex hMN)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
