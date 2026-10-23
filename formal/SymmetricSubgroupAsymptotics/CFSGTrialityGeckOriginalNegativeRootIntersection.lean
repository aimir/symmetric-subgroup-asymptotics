import SymmetricSubgroupAsymptotics.CFSGTrialityGeckNegativeParabolicRootIntersection
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedPreimageCoordinates
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalUpperNormalizer
import SymmetricSubgroupAsymptotics.CFSGKernelControlledIntersection

/-! Negative simple relative root groups of the SAME original triality
model are intersections of originalNegative with the two actual minimal
positive parabolics. The central kernel lies in each parabolic; therefore
these intersections descend without assuming faithful whole-J action. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalNegativeRootIntersection
open CFSGTrialityGeckNegativeParabolicRootIntersection
open CFSGTrialityGeckGeneratedPreimageCoordinates CFSGTrialityGeckGeneratedOriginalProjection
open CFSGTrialityGeckOriginalOppositeAlignment CFSGTrialityGeckOriginalUpperNormalizer
open CFSGTrialityGeckGeneratedParabolics CFSGTrialityGeckRelativeRootGenerated
open CFSGKernelControlledIntersection CFSGSerreOrdinaryTwists

def originalNegativeOrbitRoot (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (a : Bool) :
    Subgroup (CFSG.Models.TrialityD4 q) :=
  (negativeOrbitRootGenerated q a).map (generatedToOriginal q)

theorem original_kernel_le_parabolicGenerated (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (a : Bool) :
    (generatedToOriginal q).ker≤
      parabolicGenerated (q.Extension 3) (definingFieldAutomorphism q 3) a :=
  (original_kernel_le_upperGenerated q).trans
    (upperGenerated_lt_parabolicGenerated (q.Extension 3) (definingFieldAutomorphism q 3) a).le

theorem original_negative_inf_simpleParabolic (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (a : Bool) :
    originalNegative q⊓originalSimpleParabolic q a=originalNegativeOrbitRoot q a := by
  have hh := congrArg (fun S : Subgroup
      (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3))=>
        S.map (generatedToOriginal q)) (negative_rootPart_inf_parabolicGenerated q a)
  dsimp only at hh
  rw [map_inf_eq_of_kernel_le_right (generatedToOriginal q) _ _
    (original_kernel_le_parabolicGenerated q a),rootPart_negative_original_image] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalNegativeRootIntersection
