import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckImageSemilinearTwist

/-! Covariance of the entire literal matrix group on the SAME original
E6 image under the actual matrix and image twists. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckMatrixActionCovariance
open CFSGTwistedE6GeckImageSemilinearTwist CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckDiagramCovariance

theorem matrix_action_covariance (K : Type) [Field K] (sigma : K≃+*K) (g : MatrixGroup K) :
    imageAmbientTwist K sigma (matrixAction K g)=matrixAction K (matrixGroupTwist K sigma g) := by
  apply LinearEquiv.ext
  intro y
  obtain ⟨x,rfl⟩ := (imageSemilinearEquiv K sigma).surjective y
  rw [imageAmbientTwist_apply,LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [imageSemilinearEquiv_val,matrixAction_apply,matrixAction_apply,imageSemilinearEquiv_val]
  change matrixTwist K sigma ((g.val : Matrix GeckIndex GeckIndex K)*x.val*
      (↑(g.val⁻¹) : Matrix GeckIndex GeckIndex K))=
    matrixTwist K sigma (g.val : Matrix GeckIndex GeckIndex K)*matrixTwist K sigma x.val*
      matrixTwist K sigma (↑(g.val⁻¹) : Matrix GeckIndex GeckIndex K)
  rw [map_mul,map_mul]

theorem matrix_action_covariance_hom (K : Type) [Field K] (sigma : K≃+*K) :
    (imageAmbientTwist K sigma).toMonoidHom.comp (matrixAction K)=
      (matrixAction K).comp (matrixGroupTwist K sigma).toMonoidHom := by
  apply MonoidHom.ext
  exact matrix_action_covariance K sigma

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckMatrixActionCovariance
