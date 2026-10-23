import SymmetricSubgroupAsymptotics.CFSGTrialityGeckActionRangeTwist
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMatrixActionCentralKernel
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRawActionKernel
import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent

/-! The SAME transported-image matrix action is nontrivial and faithful
on literal U. Nontriviality follows from the checked raw noncentral Weyl
witness and the proved transported-action central kernel; U faithfulness
then uses the actual positive-quotient injectivity theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckPositiveActionInjective
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckActionRangeTwist
open CFSGTrialityGeckMatrixActionCentralKernel CFSGTrialityGeckRawActionKernel
open CFSGTrialityGeckRootAction CFSGTrialityGeckPositiveTwist

theorem raw_weyl_not_center (K : Type) [Field K] (i : Fin 4) :
    CFSGNormTwoGeckImageWeylWitness.weylElement (CartanMatrix.D 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite Base Index K i ∉
        Subgroup.center (MatrixGroup K) := by
  intro hc
  have hm := CFSGSimpleProjectiveDescent.map_mem_center
    (rawAction K).rangeRestrict (rawAction K).rangeRestrict_surjective _ hc
  exact CFSGNormTwoGeckImageWeylWitness.imageWeyl_not_center (CartanMatrix.D 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite Base Index simple_sign K i hm

theorem actionRange_nontrivial (K : Type) [Field K] : Nontrivial (ActionRange K) := by
  let w : MatrixGroup K := CFSGNormTwoGeckImageWeylWitness.weylElement
    (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite Base Index K 0
  have hne : matrixRangeProjection K w ≠ 1 := by
    intro h
    exact raw_weyl_not_center K 0 (matrixRangeProjection_kernel_le_center K h)
  exact ⟨⟨matrixRangeProjection K w, 1, hne⟩⟩

theorem positiveAction_injective (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] : Function.Injective (positiveAction K) := by
  letI : Nontrivial (ActionRange K) := actionRange_nontrivial K
  have hi := CFSGNormTwoCoordinatePositiveQuotientInjectivity.positive_quotient_injective
    (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K p
    (matrixRangeProjection K) (matrixRangeProjection_surjective K)
  intro u v huv
  apply hi
  apply Subtype.ext
  exact huv

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckPositiveActionInjective
