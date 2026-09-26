import SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairPilot

/-! Bounded scalar pair-table rows 7, 8, 9, 10, 11, 12. Each declaration
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

theorem row07_le (j : Fin 41) :
    (displayedRows 7).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 7) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 7) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨4, 7, 4, 4, 4, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (2 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (5 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row08_le (j : Fin 41) :
    (displayedRows 8).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 8) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 8) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨4, 8, 4, 4, 3, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (2 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (5 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row09_le (j : Fin 41) :
    (displayedRows 9).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 9) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 9) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨5, 11, 3, 3, 1, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (2 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (0 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row10_le (j : Fin 41) :
    (displayedRows 10).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 10) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 10) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨5, 11, 4, 4, 0, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (2 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (1 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row11_le (j : Fin 41) :
    (displayedRows 11).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 11) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 11) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨6, 12, 3, 3, 0, 0⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (2 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (1 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem row12_le (j : Fin 41) :
    (displayedRows 12).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 12) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 12) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  change (⟨0, 0, 0, 0, 1, 3⟩ : JointCapacityRow).polygonPairBudget (displayedRows j) ≤
    (4 * (1 : ℝ)) * (4 * displayedScale j) * pairMatrix64 (2 : Fin 6) (displayedColor j) / 64
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

end SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairs
