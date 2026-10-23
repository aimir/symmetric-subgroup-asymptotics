import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSourceWordAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateImageCentralKernel

/-! Typed raw-action boundaries for the checked D4 coordinate kernel
theorem. These avoid repeatedly unfolding the source-Cartan realization
inside later transported-image proofs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckRawActionKernel
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckDiagramCovariance
open CFSGTrialityD4NormTwo CFSGSerreQuadraticMatrix CFSGTrialityGeckRootAction

def rawAction (K : Type) [Field K] : MatrixGroup K →*
    ((baseChange rawData K).range ≃ₗ[K] (baseChange rawData K).range) :=
  CFSGNormTwoGeckImageWeylWitness.imageAction (CartanMatrix.D 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite Base Index simple_sign K

theorem rawAction_apply (K : Type) [Field K] (g : MatrixGroup K)
    (y : (baseChange rawData K).range) :
    (rawAction K g y).val = (g.val : Matrix GeckIndex GeckIndex K) * y.val *
      (↑(g.val⁻¹) : Matrix GeckIndex GeckIndex K) := rfl

theorem rawAction_kernel_le_center (K : Type) [Field K] :
    (rawAction K).ker ≤ Subgroup.center (MatrixGroup K) :=
  CFSGNormTwoCoordinateImageCentralKernel.imageAction_kernel_le_center
    (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckRawActionKernel
