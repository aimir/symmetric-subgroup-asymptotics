import SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairPilot

/-! Bounded scalar pair-table rows 19, 20, 21, 22, 23, 24. Each declaration
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

theorem row19_le (j : Fin 41) :
    (displayedRows 19).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 19) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 19) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨2, 5, 2, 2, 1, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (5 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row20_le (j : Fin 41) :
    (displayedRows 20).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 20) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 20) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨3, 6, 2, 2, 0, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (1 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row21_le (j : Fin 41) :
    (displayedRows 21).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 21) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 21) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨0, 0, 0, 0, 1, 3⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (2 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row22_le (j : Fin 41) :
    (displayedRows 22).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 22) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 22) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨1, 1, 1, 0, 1, 2⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (3 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row23_le (j : Fin 41) :
    (displayedRows 23).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 23) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 23) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨1, 2, 1, 1, 2, 1⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (4 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row24_le (j : Fin 41) :
    (displayedRows 24).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 24) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 24) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨1, 3, 1, 1, 1, 1⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (4 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

end SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairs
