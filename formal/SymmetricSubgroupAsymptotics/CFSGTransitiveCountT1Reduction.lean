import SymmetricSubgroupAsymptotics.CFSGSevenTargetsONBinaryGoodSylow
import SymmetricSubgroupAsymptotics.CFSGTransitiveSubquadraticCount

/-! Successor T1 endpoint with the labelled transitive subgroup-count
input proved from CFSG internally. The three other published bundles
and the two explicitly restricted simple-model callbacks remain inputs.
This is not a CFSG-only proof of T1. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

theorem T1_of_three_published_inputs_cfsg_and_remaining_after_ON_binary
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterONBinary i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuTwentyFourComplete i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : T1 :=
  T1_of_four_published_inputs_cfsg_and_remaining_after_ON_binary
    lit hExceptionalOrbits (CFSGTransitiveSubquadraticCount.transitiveCountInput_proved hCFSG)
    hTracey hCFSG remainingGoodSylow remainingSimpleIndex

theorem allTargets_of_three_published_inputs_cfsg_and_remaining_after_ON_binary
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hTracey : TraceyPublished2018PermutationInputBundle)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterONBinary i →
        ∃ p, CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuTwentyFourComplete i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_three_published_inputs_cfsg_and_remaining_after_ON_binary
      lit hExceptionalOrbits hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
