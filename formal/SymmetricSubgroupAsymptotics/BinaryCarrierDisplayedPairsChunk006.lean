import SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairPilot

/-! Bounded scalar pair-table rows 37, 38, 39, 40. Each declaration
checks one literal displayed row against its 41 original columns.
No actual normal-subgroup coverage or physical weighting is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairs

open BinaryCarrierCone BinaryCarrierStarEnvelope BinaryCarrierDisplayedPairTable

private theorem vec_six_zero {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (0 : Fin 6) = a := rfl

private theorem vec_six_one {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (1 : Fin 6) = b := rfl

private theorem vec_six_two {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (2 : Fin 6) = c := rfl

private theorem vec_six_three {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (3 : Fin 6) = d := rfl

private theorem vec_six_four {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (4 : Fin 6) = e := rfl

private theorem vec_six_five {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

theorem row37_le (j : Fin 41) :
    (displayedRows 37).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 37) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 37) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨2, 4, 2, 1, 3, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (5 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row38_le (j : Fin 41) :
    (displayedRows 38).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 38) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 38) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨2, 5, 2, 1, 2, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (5 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row39_le (j : Fin 41) :
    (displayedRows 39).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 39) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 39) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨2, 6, 2, 2, 1, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (5 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row40_le (j : Fin 41) :
    (displayedRows 40).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 40) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 40) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨3, 7, 2, 2, 0, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (1 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

end SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairs
