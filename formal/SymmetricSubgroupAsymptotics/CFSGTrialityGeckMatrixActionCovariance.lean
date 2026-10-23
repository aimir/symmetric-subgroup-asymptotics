import SymmetricSubgroupAsymptotics.CFSGTrialityGeckImageSemilinearTwist
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMatrixGroupTwist

/-! Covariance of the entire natural elementary action on the SAME
original image under the actual matrix and image twists. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMatrixActionCovariance
open CFSGTrialityGeckImageSemilinearTwist CFSGTrialityGeckMatrixGroupTwist
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckDiagramCovariance

theorem matrix_action_covariance (K : Type) [Field K] (σ : K ≃+* K) (g : MatrixGroup K) :
    imageAmbientTwist K σ (matrixAction K g) = matrixAction K (matrixGroupTwist K σ g) := by
  apply LinearEquiv.ext
  intro y
  obtain ⟨x,rfl⟩ := (imageSemilinearEquiv K σ).surjective y
  rw [imageAmbientTwist_apply,LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [imageSemilinearEquiv_val,matrixAction_apply,matrixAction_apply,imageSemilinearEquiv_val]
  change matrixTwist K σ ((g.val : Matrix GeckIndex GeckIndex K)*x.val*
      (↑(g.val⁻¹) : Matrix GeckIndex GeckIndex K)) =
    matrixTwist K σ (g.val : Matrix GeckIndex GeckIndex K) * matrixTwist K σ x.val *
      matrixTwist K σ (↑(g.val⁻¹) : Matrix GeckIndex GeckIndex K)
  rw [map_mul,map_mul]

theorem matrix_action_covariance_hom (K : Type) [Field K] (σ : K ≃+* K) :
    (imageAmbientTwist K σ).toMonoidHom.comp (matrixAction K) =
      (matrixAction K).comp (matrixGroupTwist K σ).toMonoidHom := by
  apply MonoidHom.ext
  exact matrix_action_covariance K σ

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMatrixActionCovariance
