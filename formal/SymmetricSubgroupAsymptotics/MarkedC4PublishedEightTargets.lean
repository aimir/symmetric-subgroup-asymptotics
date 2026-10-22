import SymmetricSubgroupAsymptotics.CFSGSufficientPublishedTargetsCombined

/-! Public targets with eight independent published inputs. The simple-index
input supplies the required automorphism count, and actual affine orders and
socle quotients supply the primitive relative ternary-head bound. Neither
simple two-generation nor primitive normal generation is a parameter.
The CFSG model reductions are optional and are not assumed by these exports. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4
open MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_eight_published_inputs
    (lit : PreE7CharacterPublishedInputs)
    (hcomp : PrimitiveCompositionLengthInput)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleIndex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (hMN : McIverNeumannPermutationGeneratorBound) : T1 :=
  T1_of_seven_published_inputs_and_sufficientSimpleIndex
    lit hcomp hAG hExceptionalOrbits hLMM hTraceyPerm hMN
    (PrimitiveSocleRawStructure.sufficientSimpleIndexBounds_of_published hSimpleIndex)

theorem allTargets_of_eight_published_inputs
    (lit : PreE7CharacterPublishedInputs)
    (hcomp : PrimitiveCompositionLengthInput)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleIndex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (hMN : McIverNeumannPermutationGeneratorBound) : AllTargets :=
  allTargets_iff_T1.mpr (T1_of_eight_published_inputs
    lit hcomp hAG hExceptionalOrbits hLMM hTraceyPerm hSimpleIndex hMN)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
