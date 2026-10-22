import SymmetricSubgroupAsymptotics.CFSGSufficientPublishedTargetsOrder
import SymmetricSubgroupAsymptotics.CFSGUnitaryGoodSylowReductionCurrent
import SymmetricSubgroupAsymptotics.CFSGExceptionalSufficientSimpleIndexReduction

/-! The actual T1 residual after whole twisted-A GoodSylow and complete
untwisted exceptional-E sufficient simple-index proofs. Five published
inputs and two genuine remaining model obligations are explicit.
This is not a CFSG-only theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_five_published_inputs_cfsg_and_remaining_after_unitary_E
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterUnitary i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterExceptionalE i →
        CFSGReduction.ModelSufficientSimpleIndexBounds i) : T1 :=
  T1_of_six_published_inputs_and_sufficientSimpleIndex lit
    (CFSGReduction.aschbacherGuralnick_of_cfsg_and_remaining_after_unitary hCFSG remainingGoodSylow)
    hExceptionalOrbits hLMM hTraceyPerm hMN
    (CFSGReduction.sufficientSimpleIndexBounds_of_cfsg_and_remaining_after_exceptional_E hCFSG remainingSimpleIndex)

theorem allTargets_of_five_published_inputs_cfsg_and_remaining_after_unitary_E
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterUnitary i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterExceptionalE i →
        CFSGReduction.ModelSufficientSimpleIndexBounds i) : AllTargets :=
  allTargets_iff_T1.mpr (T1_of_five_published_inputs_cfsg_and_remaining_after_unitary_E
    lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
