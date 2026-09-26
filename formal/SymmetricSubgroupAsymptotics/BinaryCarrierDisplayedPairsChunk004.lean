import SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairPilot

/-! Bounded scalar pair-table rows 25, 26, 27, 28, 29, 30. Each declaration
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

theorem row25_le (j : Fin 41) :
    (displayedRows 25).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 25) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 25) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨1, 3, 1, 1, 3, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (4 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row26_le (j : Fin 41) :
    (displayedRows 26).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 26) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 26) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨1, 4, 1, 1, 2, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (4 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row27_le (j : Fin 41) :
    (displayedRows 27).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 27) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 27) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨1, 5, 1, 2, 1, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (5 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row28_le (j : Fin 41) :
    (displayedRows 28).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 28) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 28) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨2, 4, 1, 1, 2, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (5 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row29_le (j : Fin 41) :
    (displayedRows 29).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 29) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 29) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨2, 5, 1, 1, 1, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (5 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row30_le (j : Fin 41) :
    (displayedRows 30).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 30) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 30) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨2, 6, 1, 2, 0, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (1 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

end SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairs
