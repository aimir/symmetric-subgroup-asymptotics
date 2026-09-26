import SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairPilot

/-! Bounded scalar pair-table rows 0, 2, 3, 4, 5, 6. Each declaration
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

theorem row00_le (j : Fin 41) :
    (displayedRows 0).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 0) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 0) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨0, 0, 0, 0, 1, 6⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (2 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (2 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row02_le (j : Fin 41) :
    (displayedRows 2).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 2) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 2) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨1, 2, 1, 1, 4, 4⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (2 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (4 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row03_le (j : Fin 41) :
    (displayedRows 3).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 3) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 3) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨2, 3, 2, 2, 3, 3⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (2 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (4 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row04_le (j : Fin 41) :
    (displayedRows 4).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 4) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 4) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨2, 4, 2, 2, 4, 2⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (2 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (4 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row05_le (j : Fin 41) :
    (displayedRows 5).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 5) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 5) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨3, 6, 3, 3, 6, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (2 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (5 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row06_le (j : Fin 41) :
    (displayedRows 6).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 6) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 6) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨4, 6, 4, 4, 5, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (2 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (5 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

end SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairs
