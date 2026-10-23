import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckSimpleRootRanges
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalParabolicAction
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGKernelControlledIntersection

/-! The two full negative simple ranges of the original G2 group are
its actual negative subgroup intersected with the two minimal positive
parabolics. A pair-preserving automorphism permutes these ranges; the
Bool permutation is retained in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalNegativeRootAction
open CFSGGTwoD4GeckSimpleRootRanges CFSGGTwoD4GeckOriginalSimpleParameters
open CFSGGTwoD4GeckSimpleParameters CFSGGTwoD4GeckOriginalProjection
open CFSGGTwoD4GeckOriginalParabolicAction CFSGGTwoD4GeckOriginalUpperNormalizer
open CFSGGTwoD4GeckOriginalOppositeAlignment CFSGGTwoD4GeckNegativeParabolicIntersection
open CFSGTrialityGeckGeneratedParabolics CFSGTrialityGeckRelativeRootGenerated
open CFSGKernelControlledIntersection CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] [IsSimpleGroup (Projective CartanMatrix.G₂ K)]

theorem original_negative_range_generated (a : Bool) :
    (negativeOrbitRootGenerated K a).map (generatedToOriginal K) =
      (originalSimpleHom K true a).range :=
  (congrArg (fun S : Subgroup (fixedRootGenerated K (RingEquiv.refl K)) =>
    S.map (generatedToOriginal K)) (negative_generated_eq_range K a)).trans
      (MonoidHom.range_comp (generatedToOriginal K) (simpleGeneratedHom K true a)).symm

theorem original_positive_range_generated (a : Bool) :
    (positiveOrbitRootGenerated K a).map (generatedToOriginal K) =
      (originalSimpleHom K false a).range :=
  (congrArg (fun S : Subgroup (fixedRootGenerated K (RingEquiv.refl K)) =>
    S.map (generatedToOriginal K)) (positive_generated_eq_range K a)).trans
      (MonoidHom.range_comp (generatedToOriginal K) (simpleGeneratedHom K false a)).symm

theorem original_kernel_le_parabolicGenerated (a : Bool) :
    (generatedToOriginal K).ker ≤ parabolicGenerated K (RingEquiv.refl K) a :=
  (original_kernel_le_upperGenerated K).trans
    (upperGenerated_lt_parabolicGenerated K (RingEquiv.refl K) a).le

theorem original_negative_inf_simpleParabolic (a : Bool) :
    originalNegative K ⊓ originalSimpleParabolic K a = (originalSimpleHom K true a).range := by
  have hh := congrArg (fun S : Subgroup (fixedRootGenerated K (RingEquiv.refl K)) =>
    S.map (generatedToOriginal K)) (negative_rootPart_inf_parabolicGenerated K a)
  dsimp only at hh
  rw [map_inf_eq_of_kernel_le_right (generatedToOriginal K) _ _
    (original_kernel_le_parabolicGenerated K a), original_negative_range_generated] at hh
  exact hh

theorem exists_original_negative_root_permutation (p : ℕ) [Fact p.Prime] [CharP K p]
    (f : MulAut (Projective CartanMatrix.G₂ K))
    (hU : (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)).map
      f.toMonoidHom = (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)))
    (hV : (originalNegative K).map f.toMonoidHom = originalNegative K) :
    ∃ sigma : Equiv.Perm Bool, ∀ a : Bool,
      (originalSimpleHom K true a).range.map f.toMonoidHom =
        (originalSimpleHom K true (sigma a)).range := by
  obtain ⟨sigma, hsigma⟩ := exists_original_parabolic_permutation K p f hU
  refine ⟨sigma, ?_⟩
  intro a
  rw [←original_negative_inf_simpleParabolic, Subgroup.map_inf _ _ _ f.injective,
    hV, hsigma a, original_negative_inf_simpleParabolic]

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalNegativeRootAction
