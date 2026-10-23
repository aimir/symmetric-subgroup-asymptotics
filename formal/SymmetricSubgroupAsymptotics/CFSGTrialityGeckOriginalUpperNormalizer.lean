import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedParabolics
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedOriginalCentralKernel
import SymmetricSubgroupAsymptotics.CoprimeTernaryCentralizerLift

/-! The intrinsic upper normalizer of J maps onto the literal ORIGINAL
positive Sylow normalizer. The original kernel is contained in this
upper normalizer, so the subgroup correspondence applies to all its
overgroups. No original automorphism is lifted. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalUpperNormalizer
open CFSGTrialityGeckGeneratedParabolics CFSGTrialityGeckGeneratedOriginalCentralKernel
open CFSGTrialityGeckGeneratedPositiveSylow CFSGTrialityGeckGeneratedOriginalProjection
open CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckOriginalRootFamily
open CFSGTrialityGeckRootGeneratedPGroup CFSGTrialityGeckFixedPositiveImageSylow CFSGSerreOrdinaryTwists
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

def originalSimpleParabolic (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (a : Bool) : Subgroup (CFSG.Models.TrialityD4 q) :=
  (parabolicGenerated (q.Extension 3) (definingFieldAutomorphism q 3) a).map (generatedToOriginal q)

theorem upperGenerated_map_original (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    (upperGenerated (q.Extension 3) (definingFieldAutomorphism q 3)).map (generatedToOriginal q)=
      Subgroup.normalizer (originalSylow q : Set (CFSG.Models.TrialityD4 q)) := by
  have h := CoprimeTernaryCentralizerLift.sylow_map_normalizer_eq
    (generatedToOriginal q) (generatedToOriginal_surjective q) (generatedPositiveSylow q)
  rw [←(generatedPositiveSylow q).coe_coe,generatedPositiveSylow_coe,
    rootPart_positive_original_image] at h
  rw [upperGenerated_eq_normalizer]
  exact h

theorem original_kernel_le_upperGenerated (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    (generatedToOriginal q).ker≤upperGenerated (q.Extension 3) (definingFieldAutomorphism q 3) := by
  rw [upperGenerated_eq_normalizer]
  exact (generatedToOriginal_kernel_le_center q).trans
    (Subgroup.center_le_normalizer (rootPart (q.Extension 3) (definingFieldAutomorphism q 3) false :
      Set (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3))))

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalUpperNormalizer
