import SymmetricSubgroupAsymptotics.CFSGSevenTargetsUnitaryRankTwo
import SymmetricSubgroupAsymptotics.CFSGTwistedDGoodSylowModelReduction

/-! T1 with the complete original twisted-D good-Sylow branch discharged.
The remaining model obligations are explicit; this is not yet a theorem
from CFSG alone. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open MarkedC4 MarkedC4.OrdinaryNilpotentGeneration

theorem T1_of_five_published_inputs_cfsg_and_remaining_after_twistedD
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterTwistedD i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterUnitaryRankTwo i →
        CFSGReduction.ModelBoundsAfterUnitarySquare i) : T1 :=
  T1_of_five_published_inputs_cfsg_and_remaining_after_unitary_rankTwo
    lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG
    (fun i _ _ hn _ => by
      rcases CFSGReduction.model_goodSylow_or_remaining_after_twistedD i hn with h | h
      · exact h
      · exact remainingGoodSylow i hn h)
    remainingSimpleIndex

theorem allTargets_of_five_published_inputs_cfsg_and_remaining_after_twistedD
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterTwistedD i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterUnitaryRankTwo i →
        CFSGReduction.ModelBoundsAfterUnitarySquare i) : AllTargets :=
  allTargets_iff_T1.mpr (T1_of_five_published_inputs_cfsg_and_remaining_after_twistedD
    lit hExceptionalOrbits hLMM hTraceyPerm hMN hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
