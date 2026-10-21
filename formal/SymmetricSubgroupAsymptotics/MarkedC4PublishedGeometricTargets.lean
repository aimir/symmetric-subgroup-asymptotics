import SymmetricSubgroupAsymptotics.MarkedC4PublishedActualAffineTargets

/-! Public targets from twelve explicit published inputs. Exact binary
excess is proved internally. Complete original affine sources replace the
bounded composition and primitive12/16 correspondences. The normal-F
quotient theorem remains an explicit published input. Stronger unused
catalogue interfaces remain available separately. -/
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
    : T1 := by
  exact T1_of_published_inputs_actualAffineSources
    lit hcomp h57 hodd hAG hExceptionalOrbits hPrimitiveGen hLMM hTraceyPerm hSimpleGen hSimpleIndex hMN

/-- The same twelve inputs imply all three approved asymptotic targets. -/
theorem allTargets_of_published_inputs
    (lit : PreE7CharacterPublishedInputs)
    (hcomp : PrimitiveCompositionLengthInput)
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
    : AllTargets := by
  exact allTargets_of_published_inputs_actualAffineSources
    lit hcomp h57 hodd hAG hExceptionalOrbits hPrimitiveGen hLMM hTraceyPerm hSimpleGen hSimpleIndex hMN

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
