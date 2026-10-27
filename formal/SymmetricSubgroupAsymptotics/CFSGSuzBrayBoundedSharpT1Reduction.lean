import SymmetricSubgroupAsymptotics.CFSGSuzBrayT1Reduction
import SymmetricSubgroupAsymptotics.TraceyPublished2018BoundedSharpCFSG

/-! The bounded-sharp published field is filled internally. The remaining
three published inputs are GM, exceptional orbits, and coarse Tracey.
The exact existing Good13 and numerical21 callbacks are retained.
The literal J2 frame and same-factor exclusion supply the final bounded
sharp case. No sharp-generator or model-recognition hypothesis is added. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

theorem T1_of_three_published_inputs_cfsg_and_remaining_after_suz_bray_bounded_sharp
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hTracey : TraceyPermutationGeneratorInput)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterSuzBray i →
        ∃ p,CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuTwentyFourComplete i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : T1 :=
  T1_of_three_published_inputs_cfsg_and_remaining_after_suz_bray
    lit hExceptionalOrbits
    (TraceyPublished2018BoundedSharpCFSG.inputBundle_of_coarse hCFSG hTracey)
    hCFSG remainingGoodSylow remainingSimpleIndex

theorem allTargets_of_three_published_inputs_cfsg_and_remaining_after_suz_bray_bounded_sharp
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hTracey : TraceyPermutationGeneratorInput)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterSuzBray i →
        ∃ p,CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuTwentyFourComplete i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_three_published_inputs_cfsg_and_remaining_after_suz_bray_bounded_sharp
      lit hExceptionalOrbits hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
