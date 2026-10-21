import SymmetricSubgroupAsymptotics.CFSGGTwoImageFourthCoefficient
import SymmetricSubgroupAsymptotics.CFSGGTwoRootUnits
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrixActions

/-! The original G₂ model and the literal folded root units act on the
SAME base-changed integral matrix image. No faithfulness or recognition
of the natural eight-dimensional group is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
open CFSG.Models.Chevalley

 theorem rootTransvection_val_data (K : Type) [Field K] (neg : Bool) (i : Fin 2) (t : K) :
    (rootTransvection K neg i t : Mat K)=
      1+t • CFSGSerreQuadraticMatrix.fieldRoot realizationData K neg i+
        t^2 • CFSGSerreQuadraticMatrix.fieldSecond realizationData K neg i := by
  rw [realizationData_fieldRoot,realizationData_fieldSecond]
  rfl

 theorem rootTransvection_inv_val_data (K : Type) [Field K] (neg : Bool) (i : Fin 2) (t : K) :
    (↑((rootTransvection K neg i t)⁻¹):Mat K)=
      1-t • CFSGSerreQuadraticMatrix.fieldRoot realizationData K neg i+
        t^2 • CFSGSerreQuadraticMatrix.fieldSecond realizationData K neg i := by
  rw [realizationData_fieldRoot,realizationData_fieldSecond]
  exact rootTransvection_inv_val K neg i t

 theorem image_fourth_zero (K : Type) [Field K] (neg : Bool) (i : Fin 2)
    (x : Space CartanMatrix.G₂ K) :
    CFSGSerreQuadraticMatrix.fieldSecond realizationData K neg i*foldedBaseChange K x*
      CFSGSerreQuadraticMatrix.fieldSecond realizationData K neg i=0 := by
  simp only [realizationData_fieldSecond]
  exact baseChange_image_fourth_coefficient_zero K neg i x

 abbrev foldedImageRepresentation (K : Type) [Field K] :=
  CFSGSerreQuadraticMatrix.imageRepresentation realizationData K

 abbrev naturalGroup (K : Type) [Field K] :=
  CFSGSerreQuadraticMatrix.elementaryGroup K (rootTransvection K)

 abbrev naturalImageAction (K : Type) [Field K] :=
  CFSGSerreQuadraticMatrix.elementaryImageAction realizationData K (rootTransvection K)
    (rootTransvection_val_data K) (rootTransvection_inv_val_data K) (image_fourth_zero K)

 theorem action_ranges_eq (K : Type) [Field K] :
    (foldedImageRepresentation K).range=(naturalImageAction K).range :=
  CFSGSerreQuadraticMatrix.action_ranges_eq realizationData K (rootTransvection K)
    (rootTransvection_val_data K) (rootTransvection_inv_val_data K) (image_fourth_zero K)

 abbrev naturalRoot (K : Type) [Field K] :=
  CFSGSerreQuadraticMatrix.elementaryRoot K (rootTransvection K)

 def naturalLongWeyl (K : Type) [Field K] : naturalGroup K :=
  naturalRoot K false 1 (-1)*naturalRoot K true 1 1*naturalRoot K false 1 (-1)

 theorem naturalLongWeyl_val (K : Type) [Field K] : (naturalLongWeyl K).val=longWeyl K := rfl

 theorem naturalLongWeyl_four (K : Type) [Field K] : naturalLongWeyl K^4=1 := by
  apply Subtype.ext
  change (naturalLongWeyl K).val^4=1
  rw [naturalLongWeyl_val,longWeyl_four]

end SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
