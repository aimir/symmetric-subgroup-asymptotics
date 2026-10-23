import SymmetricSubgroupAsymptotics.CFSGPGeneratedCentralKernel
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckGeneratedPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalOppositeAlignment

/-! The literal map from J to the ORIGINAL twisted E6 projective group
has central kernel. The original action kernel is central, while the
second central-quotient layer is controlled by actual p-group generation
and the injective positive Sylow. No perfectness or whole-source
faithfulness is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalCentralKernel
open CFSGTwistedE6GeckGeneratedPositiveSylow CFSGTwistedE6GeckOriginalOppositeAlignment
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6OriginalGoodSylow
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckRootGeneratedPGroup
open CFSGTwistedE6GeckFixedRangePreimage CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6GeckDerivedRootGeneration CFSGTwistedE6FixedA2 CFSGSerreOrdinaryTwists
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

theorem generatedToDerived_kernel_le_center (q : CFSG.PrimePower) :
    (generatedToDerived q).ker≤Subgroup.center
      (fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2)) := by
  intro g hg
  let inc := Subgroup.inclusion (fixedRootGenerated_le_matrixGroup
    (q.Extension 2) (definingFieldAutomorphism q 2))
  have ha : matrixAction (q.Extension 2) (inc g)=1 :=
    congrArg (fun z : (derivedImageAction q).range=>z.val) hg
  have hc := matrixAction_kernel_le_center (q.Extension 2) ha
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact congrArg (fun z : MatrixGroup (q.Extension 2)=>z.val)
    (Subgroup.mem_center_iff.mp hc (inc x))

theorem original_kernel_le_action_center (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    (generatedToOriginal q).ker≤(Subgroup.center (derivedImageAction q).range).comap
      (generatedToDerived q) := by
  intro g hg
  change generatedToDerived q g∈Subgroup.center (derivedImageAction q).range
  have hi : generatedToDerived q g∈(imageToOriginal q).ker := hg
  rwa [imageToOriginal_kernel] at hi

theorem generatedToOriginal_kernel_le_center (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    (generatedToOriginal q).ker≤Subgroup.center
      (fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2)) := by
  apply CFSGPGeneratedCentralKernel.kernel_le_center_of_injective_sylow
    (generatedToDerived q) (generatedToDerived_kernel_le_center q)
    (generatedToOriginal q) (original_kernel_le_action_center q) (generatedPositiveSylow q)
  · rw [generatedPositiveSylow_coe]
    exact rootPart_positive_original_injective q
  · exact rootPart_isPGroup (q.Extension 2) (definingFieldAutomorphism q 2) q.prime false
  · exact rootPart_isPGroup (q.Extension 2) (definingFieldAutomorphism q 2) q.prime true
  · exact rootPart_sup (q.Extension 2) (definingFieldAutomorphism q 2)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalCentralKernel
