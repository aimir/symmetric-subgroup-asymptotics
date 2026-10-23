import SymmetricSubgroupAsymptotics.CFSGPGeneratedCentralKernel
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedOriginalProjection
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOppositeSylows

/-! The map from literal J to the SAME original projective triality
model has central kernel. The second central layer is controlled by
actual root p-group generation and an injective Sylow restriction,
without assuming perfectness or faithfulness of the whole action. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedOriginalCentralKernel
open CFSGTrialityGeckGeneratedPositiveSylow CFSGTrialityGeckGeneratedOriginalProjection
open CFSGTrialityGeckGoodSylow CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckRootGeneratedPGroup CFSGTrialityGeckFixedRangePreimage
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckMatrixActionCentralKernel
open CFSGTrialityGeckFixedPositiveImageSylow CFSGTrialityGeckOriginalOppositeSylows
open CFSGTrialityGeckOriginalIndexSquare CFSGSerreOrdinaryTwists
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

theorem generatedToDerived_kernel_le_center (q : CFSG.PrimePower) :
    (generatedToDerived q).ker ≤ Subgroup.center
      (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)) := by
  intro g hg
  let inc := Subgroup.inclusion (fixedRootGenerated_le_matrixGroup
    (q.Extension 3) (definingFieldAutomorphism q 3))
  have ha : matrixAction (q.Extension 3) (inc g) = 1 :=
    congrArg (fun z : DerivedImage q => z.val) hg
  have hc := matrixAction_kernel_le_center (q.Extension 3) ha
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact congrArg (fun z : MatrixGroup (q.Extension 3) => z.val)
    (Subgroup.mem_center_iff.mp hc (inc x))

theorem original_kernel_le_action_center (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    (generatedToOriginal q).ker ≤ (Subgroup.center (DerivedImage q)).comap (generatedToDerived q) := by
  intro g hg
  change generatedToDerived q g ∈ Subgroup.center (DerivedImage q)
  have hi : generatedToDerived q g ∈ (originalProjection q).ker := hg
  exact originalProjection_kernel_le_center q hi

theorem generatedToOriginal_kernel_le_center (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    (generatedToOriginal q).ker ≤ Subgroup.center
      (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)) := by
  apply CFSGPGeneratedCentralKernel.kernel_le_center_of_injective_sylow
    (generatedToDerived q) (generatedToDerived_kernel_le_center q)
    (generatedToOriginal q) (original_kernel_le_action_center q) (generatedPositiveSylow q)
  · rw [generatedPositiveSylow_coe]
    exact rootPart_positive_original_injective q
  · exact rootPart_isPGroup (q.Extension 3) (definingFieldAutomorphism q 3) q.prime false
  · exact rootPart_isPGroup (q.Extension 3) (definingFieldAutomorphism q 3) q.prime true
  · exact rootPart_sup (q.Extension 3) (definingFieldAutomorphism q 3)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedOriginalCentralKernel
