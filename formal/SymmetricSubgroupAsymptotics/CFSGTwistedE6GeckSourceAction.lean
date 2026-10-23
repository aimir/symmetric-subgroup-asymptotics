import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDiagramCovariance
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticTransportedAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateImageCentralKernel

/-! The literal raw E6 matrix group acts on the SAME original pinned
E6 tensor image. Its central kernel is the already checked all-characteristic
quartic-kernel theorem transported by equality of image submodules. No
original-source injectivity or fixed-point surjectivity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalGeckIntegralData
open CFSGSerreQuadraticMatrix CFSG.Models.Chevalley

abbrev MatrixGroup (K : Type) [Field K] := canonicalElementaryGroup rawData K
abbrev Image (K : Type) [Field K] := (baseChange data K).range

def matrixAction (K : Type) [Field K] : MatrixGroup K→*(Image K≃ₗ[K]Image K) :=
  CFSGSerreQuadraticTransportedAction.matrixAction E6_cartan rawData K (E6Data_fourth K)

theorem matrixAction_apply (K : Type) [Field K] (g : MatrixGroup K) (y : Image K) :
    (matrixAction K g y).val=(g.val : Matrix GeckIndex GeckIndex K)*y.val*
      (↑(g.val⁻¹) : Matrix GeckIndex GeckIndex K) := rfl

theorem transported_root_eq (K : Type*) [CommRing K] (neg : Bool) (i : Fin 6) (t : K) :
    canonicalRoot data K neg i t=canonicalRoot rawData K neg i t :=
  CFSGSerreQuadraticTransportedAction.transported_root_eq E6_cartan rawData K neg i t

theorem source_root_action (K : Type) [Field K] (neg : Bool) (i : Fin 6) (t : K) :
    imageRepresentation data K (CFSGSerreModelRootGeneration.modelRoot CartanMatrix.E₆ K neg i t)=
      matrixAction K (canonicalElementaryRoot rawData K neg i t) :=
  CFSGSerreQuadraticTransportedAction.source_root_action E6_cartan rawData K (E6Data_fourth K) neg i t

theorem action_ranges_eq (K : Type) [Field K] :
    (imageRepresentation data K).range=(matrixAction K).range :=
  CFSGSerreQuadraticTransportedAction.action_ranges_eq E6_cartan rawData K (E6Data_fourth K)

theorem matrixAction_kernel_le_center (K : Type) [Field K] :
    (matrixAction K).ker≤Subgroup.center (MatrixGroup K) := by
  apply CFSGSerreQuadraticTransportedAction.matrixAction_kernel_le_center E6_cartan rawData K
    (E6Data_fourth K)
    (CFSGNormTwoGeckImageFourthCoefficient.baseChange_image_fourth_coefficient_zero
      CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index E6_simple_sign K)
  exact CFSGNormTwoCoordinateImageCentralKernel.imageAction_kernel_le_center
    CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite
    CartanMatrix.E₆_off_diag_nonpos K

def matrixRangeProjection (K : Type) [Field K] : MatrixGroup K→*(matrixAction K).range :=
  (matrixAction K).rangeRestrict

theorem matrixRangeProjection_surjective (K : Type) [Field K] :
    Function.Surjective (matrixRangeProjection K) := (matrixAction K).rangeRestrict_surjective

theorem matrixRangeProjection_kernel_le_center (K : Type) [Field K] :
    (matrixRangeProjection K).ker≤Subgroup.center (MatrixGroup K) := by
  intro g hg
  exact matrixAction_kernel_le_center K (congrArg Subtype.val hg)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSourceAction
