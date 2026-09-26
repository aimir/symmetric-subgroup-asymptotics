import SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairPilot

/-! Bounded scalar pair-table rows 13, 14, 15, 16, 17, 18. Each declaration
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

theorem row13_le (j : Fin 41) :
    (displayedRows 13).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 13) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 13) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨1, 1, 1, 0, 2, 2⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (4 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row14_le (j : Fin 41) :
    (displayedRows 14).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 14) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 14) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨1, 2, 1, 1, 2, 1⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (4 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row15_le (j : Fin 41) :
    (displayedRows 15).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 15) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 15) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨1, 3, 1, 1, 1, 1⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (4 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row16_le (j : Fin 41) :
    (displayedRows 16).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 16) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 16) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨1, 4, 2, 2, 2, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (5 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row17_le (j : Fin 41) :
    (displayedRows 17).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 17) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 17) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨2, 3, 2, 1, 3, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (5 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row18_le (j : Fin 41) :
    (displayedRows 18).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 18) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 18) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨2, 4, 2, 1, 2, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (5 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

end SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairs
