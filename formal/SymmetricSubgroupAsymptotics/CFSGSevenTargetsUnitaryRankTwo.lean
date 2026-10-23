import SymmetricSubgroupAsymptotics.CFSGSevenTargetsUnitarySquare
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoSufficientSimpleIndex

/-! T1 with the rank-two unitary simple-index and outer branch fully discharged.
Higher unitary ranks and the other residual model obligations stay explicit.
Five published inputs and two residual model callbacks remain. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_five_published_inputs_cfsg_and_remaining_after_unitary_rankTwo
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
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterUnitaryRankTwo i →
        CFSGReduction.ModelBoundsAfterUnitarySquare i) : T1 :=
  T1_of_five_published_inputs_cfsg_and_remaining_after_unitary_square
    lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingGoodSylow
    (fun i _ _ hn _ => by
      rcases CFSGReduction.modelBounds_or_remaining_after_unitary_rankTwo i hn with h | h
      · exact h
      · exact remainingSimpleIndex i hn h)

theorem allTargets_of_five_published_inputs_cfsg_and_remaining_after_unitary_rankTwo
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
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterUnitaryRankTwo i →
        CFSGReduction.ModelBoundsAfterUnitarySquare i) : AllTargets :=
  allTargets_iff_T1.mpr (T1_of_five_published_inputs_cfsg_and_remaining_after_unitary_rankTwo
    lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
