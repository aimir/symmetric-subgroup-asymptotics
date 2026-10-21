import SymmetricSubgroupAsymptotics.CFSGOrthogonalBImageFourthCoefficient
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrixActions

/-! Exact action-range comparison for the original B model and the
literal quadratic-root matrix group on the SAME actual integral image.
The fourth coefficient is cancelled by its proved original-image equation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
open CFSG.Models.Chevalley

theorem rootTransvection_val_data (K : Type) [Field K] (r : ℕ) (neg : Bool) (i : Fin r) (t : K) :
    (rootTransvection K r neg i t : Mat K r)=
      1+t • CFSGSerreQuadraticMatrix.fieldRoot (realizationData r) K neg i+
      t^2 • CFSGSerreQuadraticMatrix.fieldSecond (realizationData r) K neg i := by
  rw [realizationData_fieldRoot,realizationData_fieldSecond]
  rfl

theorem rootTransvection_inv_val_data (K : Type) [Field K] (r : ℕ) (neg : Bool) (i : Fin r) (t : K) :
    (↑((rootTransvection K r neg i t)⁻¹):Mat K r)=
      1-t • CFSGSerreQuadraticMatrix.fieldRoot (realizationData r) K neg i+
      t^2 • CFSGSerreQuadraticMatrix.fieldSecond (realizationData r) K neg i := by
  rw [realizationData_fieldRoot,realizationData_fieldSecond]
  exact rootTransvection_inv_val K r neg i t

theorem image_fourth_coefficient_zero_data (K : Type) [Field K] (r : ℕ)
    (neg : Bool) (i : Fin r) (x : Space (CartanMatrix.B r).transpose K) :
    CFSGSerreQuadraticMatrix.fieldSecond (realizationData r) K neg i*
      CFSGSerreQuadraticMatrix.baseChange (realizationData r) K x*
      CFSGSerreQuadraticMatrix.fieldSecond (realizationData r) K neg i=0 := by
  simpa only [realizationData_fieldSecond] using baseChange_image_fourth_coefficient_zero K r neg i x

abbrev orthogonalImageRepresentation (K : Type) [Field K] (r : ℕ) :=
  CFSGSerreQuadraticMatrix.imageRepresentation (realizationData r) K

abbrev elementaryImageAction (K : Type) [Field K] (r : ℕ) :=
  CFSGSerreQuadraticMatrix.elementaryImageAction (realizationData r) K (rootTransvection K r)
    (rootTransvection_val_data K r) (rootTransvection_inv_val_data K r)
    (image_fourth_coefficient_zero_data K r)

theorem orthogonal_action_ranges_eq (K : Type) [Field K] (r : ℕ) :
    (orthogonalImageRepresentation K r).range=(elementaryImageAction K r).range :=
  CFSGSerreQuadraticMatrix.action_ranges_eq (realizationData r) K (rootTransvection K r)
    (rootTransvection_val_data K r) (rootTransvection_inv_val_data K r)
    (image_fourth_coefficient_zero_data K r)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
