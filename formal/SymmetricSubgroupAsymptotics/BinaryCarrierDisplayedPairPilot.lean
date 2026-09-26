import SymmetricSubgroupAsymptotics.JointCapacityPolygonBudget
import SymmetricSubgroupAsymptotics.BinaryCarrierStarEnvelope

/-! One bounded row of the displayed scalar pair table. Row 1 is the
literal H16 row (1,1,1,1,2,5), whose coupled order constraint is active.
The proof checks its 41 original columns, with original physical scales
and colors. It does not assert full pair-table or actual group coverage. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairTable

open BinaryCarrierCone BinaryCarrierStarEnvelope

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

theorem displayed_slopes_nonneg (i : Fin 41) :
    0 ≤ (displayedRows i).c ∧ 0 ≤ (displayedRows i).g := by
  fin_cases i <;> norm_num [displayedRows]

/-- This helper consumes only a rational scalar budget inequality.
It does not assume the desired support inequality. -/
theorem displayed_pair_le_of_budget (i j : Fin 41)
    (h : (displayedRows i).polygonPairBudget (displayedRows j) ≤
      (4 * displayedScale i) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor i) (displayedColor j) / 64) :
    (displayedRows i).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale i) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor i) (displayedColor j) / 64 :=
  ((displayedRows i).symmetricSupport_le_polygonPairBudget (displayedRows j)
    (displayed_slopes_nonneg i).1 (displayed_slopes_nonneg i).2
    (displayed_slopes_nonneg j).1 (displayed_slopes_nonneg j).2).trans h

theorem displayed_row_one_pair_le (j : Fin 41) :
    (displayedRows 1).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale 1) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor 1) (displayedColor j) / 64 := by
  apply displayed_pair_le_of_budget
  fin_cases j <;>
    norm_num [JointCapacityRow.polygonPairBudget, jointCapacityPolygonBudget,
      displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

end SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairTable
