import SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairPilot

/-! Bounded scalar pair-table rows 31, 32, 33, 34, 35, 36. Each declaration
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

theorem row31_le (j : Fin 41) :
    (displayedRows 31).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 31) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 31) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨0, 0, 0, 0, 1, 4⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (2 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row32_le (j : Fin 41) :
    (displayedRows 32).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 32) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 32) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨1, 1, 1, 0, 1, 3⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (3 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row33_le (j : Fin 41) :
    (displayedRows 33).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 33) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 33) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨1, 2, 1, 1, 2, 2⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (4 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row34_le (j : Fin 41) :
    (displayedRows 34).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 34) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 34) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨1, 3, 1, 1, 2, 1⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (4 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row35_le (j : Fin 41) :
    (displayedRows 35).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 35) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 35) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨1, 4, 1, 1, 1, 1⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (4 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row36_le (j : Fin 41) :
    (displayedRows 36).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 36) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 36) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨1, 5, 2, 2, 2, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (5 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

end SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairs
