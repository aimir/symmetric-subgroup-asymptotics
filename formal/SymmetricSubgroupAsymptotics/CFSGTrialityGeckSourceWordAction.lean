import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootAction
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckPositiveTwist
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveQuotientInjectivity

/-! Actual original-source and natural matrix word actions on the SAME
integral Geck image.  This records an equality of genuine actions, not
faithfulness of either representation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckSourceWordAction
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGSerreQuadraticMatrix
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckRootAction
open CFSGTrialityGeckPositiveTwist CFSGSerreQuadraticWeylWord

abbrev MatrixGroup (K : Type) [Field K] := canonicalElementaryGroup rawData K
abbrev Image (K : Type) [Field K] := (baseChange data K).range

private theorem raw_root_val (K : Type) [Field K] (neg : Bool) (i : Fin 4) (t : K) :
    (canonicalRoot rawData K neg i t : Matrix GeckIndex GeckIndex K) =
      1+t • fieldRoot data K neg i+t^2 • fieldSecond data K neg i := by
  rw [← transported_root_eq K neg i t]
  exact canonicalRoot_val data K neg i t

private theorem raw_root_inv_val (K : Type) [Field K] (neg : Bool) (i : Fin 4) (t : K) :
    (↑((canonicalRoot rawData K neg i t)⁻¹) : Matrix GeckIndex GeckIndex K) =
      1-t • fieldRoot data K neg i+t^2 • fieldSecond data K neg i := by
  rw [← transported_root_eq K neg i t]
  exact canonicalRoot_inv_val data K neg i t

def matrixAction (K : Type) [Field K] : MatrixGroup K →* (Image K ≃ₗ[K] Image K) :=
  elementaryImageAction data K (canonicalRoot rawData K) (raw_root_val K)
    (raw_root_inv_val K) (data_fourth K)

theorem matrixAction_apply (K : Type) [Field K] (g : MatrixGroup K) (y : Image K) :
    (matrixAction K g y).val = (g.val : Matrix GeckIndex GeckIndex K) * y.val *
      (↑(g.val⁻¹) : Matrix GeckIndex GeckIndex K) := rfl

theorem source_root_action (K : Type) [Field K] (neg : Bool) (i : Fin 4) (t : K) :
    imageRepresentation data K (modelRoot (CartanMatrix.D 4) K neg i t) =
      matrixAction K (canonicalElementaryRoot rawData K neg i t) :=
  source_root_action_eq_elementary data K (canonicalRoot rawData K) (raw_root_val K)
    (raw_root_inv_val K) (data_fourth K) neg i t

def positiveInclusion (K : Type) [Field K] : Positive K →* MatrixGroup K :=
  CFSGNormTwoCoordinatePositiveQuotientInjectivity.positiveInclusion
    (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K

theorem positiveInclusion_val (K : Type) [Field K] (u : Positive K) :
    (positiveInclusion K u).val = u.val := rfl

def positiveAction (K : Type) [Field K] : Positive K →* (Image K ≃ₗ[K] Image K) :=
  (matrixAction K).comp (positiveInclusion K)

def matrixRankOneWord (K : Type) [Field K] (i : Fin 4) : MatrixGroup K :=
  canonicalElementaryRoot rawData K false i 1 * canonicalElementaryRoot rawData K true i (-1) *
    canonicalElementaryRoot rawData K false i 1

def sourceRankOneWord (K : Type) [Field K] (i : Fin 4) : Model (CartanMatrix.D 4) K :=
  modelRoot (CartanMatrix.D 4) K false i 1 * modelRoot (CartanMatrix.D 4) K true i (-1) *
    modelRoot (CartanMatrix.D 4) K false i 1

theorem rank_one_action (K : Type) [Field K] (i : Fin 4) :
    imageRepresentation data K (sourceRankOneWord K i) = matrixAction K (matrixRankOneWord K i) := by
  simp only [sourceRankOneWord,matrixRankOneWord,map_mul,source_root_action]

def matrixWord (K : Type) [Field K] : List (Fin 4) → MatrixGroup K
  | [] => 1
  | i::w => matrixRankOneWord K i * matrixWord K w

def sourceWord (K : Type) [Field K] : List (Fin 4) → Model (CartanMatrix.D 4) K
  | [] => 1
  | i::w => sourceRankOneWord K i * sourceWord K w

theorem matrixWord_val (K : Type) [Field K] (w : List (Fin 4)) :
    (matrixWord K w).val = canonicalWord rawData K w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [matrixWord,Subgroup.coe_mul,ih,canonicalWord]
    rfl

theorem word_action (K : Type) [Field K] (w : List (Fin 4)) :
    imageRepresentation data K (sourceWord K w) = matrixAction K (matrixWord K w) := by
  induction w with
  | nil => simp only [sourceWord,matrixWord,map_one]
  | cons i w ih => simp only [sourceWord,matrixWord,map_mul,rank_one_action,ih]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckSourceWordAction
