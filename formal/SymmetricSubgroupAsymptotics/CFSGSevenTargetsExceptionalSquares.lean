import SymmetricSubgroupAsymptotics.CFSGSevenTargetsGTwoResidualModels
import SymmetricSubgroupAsymptotics.CFSGSufficientIndexAfterExceptionalSquares

/-! Actual T1 residual consumer after the complete G2 GoodSylow proof
and E6/E7/E8 index-square proofs. Five published inputs and two remaining
model callbacks are explicit; the E branches of the latter now ask ONLY
for outer-order budgets. This is not a CFSG-only endpoint. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_five_published_inputs_cfsg_and_remaining_after_exceptional_squares
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model →
        CFSGReduction.RemainingGoodSylowIndexWithoutClassicalSuzukiEAlternatingTwistedA2AndG2 i →
          ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexModelWithoutClassicalSuzuki i →
          CFSGReduction.SufficientSimpleIndexRemainderAfterExceptionalSquares i) : T1 := by
  apply T1_of_five_published_inputs_cfsg_and_remaining_models_after_G2 lit
    hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingGoodSylow
  intro i _ _ hn hi
  exact CFSGReduction.modelSufficientSimpleIndexBounds_of_remainder_after_exceptional_squares
    i (remainingSimpleIndex i hn hi)

theorem allTargets_of_five_published_inputs_cfsg_and_remaining_after_exceptional_squares
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model →
        CFSGReduction.RemainingGoodSylowIndexWithoutClassicalSuzukiEAlternatingTwistedA2AndG2 i →
          ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexModelWithoutClassicalSuzuki i →
          CFSGReduction.SufficientSimpleIndexRemainderAfterExceptionalSquares i) : AllTargets :=
  allTargets_iff_T1.mpr (T1_of_five_published_inputs_cfsg_and_remaining_after_exceptional_squares
    lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
