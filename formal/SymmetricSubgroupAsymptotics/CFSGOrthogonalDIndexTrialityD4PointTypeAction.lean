import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4StarCliqueAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4PointLabelCoverage

/-! The ACTUAL index-three subgroup acts on literal Q-singular points
by descending its original star-set action through PROVED connected
classes. No point action or geometric lifting is an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices
variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

theorem starLabelAction_point_eq (f : naturalPointTypeStabilizer K p) (S T : PointStarLabels K)
    (h : pointOfStar K S = pointOfStar K T) :
    pointOfStar K (starLabelAction K p f S) = pointOfStar K (starLabelAction K p f T) := by
  have hp := (pointStar_connected_iff_point_eq K S T).mpr (congrArg Subtype.val h)
  have hi := starLabelAction_shared_path K p f S T hp
  exact Subtype.ext ((pointStar_connected_iff_point_eq K _ _).mp hi)

def chosenPointStar (U : OriginalPoints K) : PointStarLabels K := Classical.choose (pointOfStar_surjective K U)

theorem chosenPointStar_spec (U : OriginalPoints K) : pointOfStar K (chosenPointStar K U) = U :=
  Classical.choose_spec (pointOfStar_surjective K U)

def pointTypeImage (f : naturalPointTypeStabilizer K p) (U : OriginalPoints K) : OriginalPoints K :=
  pointOfStar K (starLabelAction K p f (chosenPointStar K U))

theorem pointTypeImage_of_star (f : naturalPointTypeStabilizer K p) (S : PointStarLabels K) :
    pointTypeImage K p f (pointOfStar K S) = pointOfStar K (starLabelAction K p f S) :=
  starLabelAction_point_eq K p f (chosenPointStar K (pointOfStar K S)) S (chosenPointStar_spec K _)

theorem pointTypeImage_inv_cancel (f : naturalPointTypeStabilizer K p) (U : OriginalPoints K) :
    pointTypeImage K p f⁻¹ (pointTypeImage K p f U) = U := by
  change pointTypeImage K p f⁻¹ (pointOfStar K (starLabelAction K p f (chosenPointStar K U))) = U
  rw [pointTypeImage_of_star]
  have hc : starLabelAction K p f⁻¹ (starLabelAction K p f (chosenPointStar K U)) = chosenPointStar K U := by
    rw [map_inv]
    exact (starLabelAction K p f).symm_apply_apply _
  rw [hc]
  exact chosenPointStar_spec K U

def pointTypePermutation (f : naturalPointTypeStabilizer K p) : Equiv.Perm (OriginalPoints K) where
  toFun := pointTypeImage K p f
  invFun := pointTypeImage K p f⁻¹
  left_inv := pointTypeImage_inv_cancel K p f
  right_inv U := by simpa only [inv_inv] using pointTypeImage_inv_cancel K p f⁻¹ U

def pointTypeAction : naturalPointTypeStabilizer K p →* Equiv.Perm (OriginalPoints K) where
  toFun := pointTypePermutation K p
  map_one' := by
    apply Equiv.ext
    intro U
    change pointOfStar K (starLabelAction K p 1 (chosenPointStar K U)) = U
    rw [map_one]
    exact chosenPointStar_spec K U
  map_mul' f g := by
    apply Equiv.ext
    intro U
    change pointOfStar K (starLabelAction K p (f * g) (chosenPointStar K U)) =
      pointTypeImage K p f (pointTypeImage K p g U)
    rw [map_mul]
    exact (pointTypeImage_of_star K p f (starLabelAction K p g (chosenPointStar K U))).symm

theorem pointTypeAction_of_star (f : naturalPointTypeStabilizer K p) (S : PointStarLabels K) :
    pointTypeAction K p f (pointOfStar K S) = pointOfStar K (starLabelAction K p f S) :=
  pointTypeImage_of_star K p f S

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
