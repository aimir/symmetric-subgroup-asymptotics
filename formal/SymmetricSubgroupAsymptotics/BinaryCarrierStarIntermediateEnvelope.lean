import SymmetricSubgroupAsymptotics.BinaryCarrierStarEnvelope

/-! A scalar certificate for the remaining star intermediate row
(3,5,3,1,4,1). It uses the actual joint-capacity support and checks all
41 displayed partner rows, the coarse star crossing envelope, and itself.
The physical mass is 8 and the color is 5 (zero indexed). No assertion
about which original normal subgroups realize a displayed row is made. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierStarIntermediateEnvelope

open BinaryCarrierCone BinaryCarrierStarEnvelope

private theorem vec_six_last {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

private theorem vec_six_two {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (2 : Fin 6) = c := rfl

private theorem vec_six_three {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (3 : Fin 6) = d := rfl

private theorem vec_six_four {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (4 : Fin 6) = e := rfl

def intermediateEnvelope : JointCapacityRow := ⟨3, 5, 3, 1, 4, 1⟩

/-- A rectangle upper bound for the exact support in both directions.
The joint order constraint is retained in the support; relaxing it here
only increases this explicit upper bound. -/
def intermediatePairBudget (r : JointCapacityRow) : ℝ :=
  max (4 * (r.k : ℝ) + r.m) (3 * (r.c + r.g))

theorem symmetricSupport_le_budget (r : JointCapacityRow)
    (hc : 0 ≤ r.c) (hg : 0 ≤ r.g) :
    intermediateEnvelope.symmetricSupport r ≤ intermediatePairBudget r := by
  have hfirst : intermediateEnvelope.directedSupport r ≤ 4 * (r.k : ℝ) + r.m := by
    apply jointCapacitySupport_le
    intro δ ε hδ hε _
    have hd : (δ : ℝ) ≤ r.k := Nat.cast_le.mpr hδ
    have he : (ε : ℝ) ≤ r.m := Nat.cast_le.mpr hε
    change 4 * (δ : ℝ) + 1 * ε ≤ _
    linarith
  have hsecond : r.directedSupport intermediateEnvelope ≤ 3 * (r.c + r.g) := by
    apply jointCapacitySupport_le
    intro δ ε hδ hε _
    change δ ≤ 3 at hδ
    change ε ≤ 3 at hε
    have hd : (δ : ℝ) ≤ 3 := by exact_mod_cast hδ
    have he : (ε : ℝ) ≤ 3 := by exact_mod_cast hε
    have hx := mul_le_mul_of_nonneg_left hd hc
    have hy := mul_le_mul_of_nonneg_left he hg
    change r.c * (δ : ℝ) + r.g * ε ≤ _
    linarith
  exact max_le (hfirst.trans (le_max_left _ _)) (hsecond.trans (le_max_right _ _))

theorem head_le_color_five : (intermediateEnvelope.k : ℝ) ≤ 8 * alpha 5 := by
  norm_num [intermediateEnvelope, alpha, vec_six_last]

theorem second_le_color_five :
    ((max intermediateEnvelope.m intermediateEnvelope.a₂ : ℕ) : ℝ) ≤ 8 * beta 5 := by
  norm_num [intermediateEnvelope, beta, vec_six_last]

theorem self_le_color_five :
    intermediateEnvelope.symmetricSupport intermediateEnvelope ≤
      8 * 8 * pairMatrix64 5 5 / 64 := by
  apply (symmetricSupport_le_budget intermediateEnvelope
    (by norm_num [intermediateEnvelope]) (by norm_num [intermediateEnvelope])).trans
  norm_num [intermediatePairBudget, intermediateEnvelope, pairMatrix64, vec_six_last]

/-- The separately checked coarse crossing row has the same physical
mass and color, but is not a coordinatewise envelope of this row. -/
theorem coarse_cross_le_color_five :
    intermediateEnvelope.symmetricSupport coarseEnvelope ≤
      8 * 8 * pairMatrix64 5 5 / 64 := by
  apply (symmetricSupport_le_budget coarseEnvelope
    (by norm_num [coarseEnvelope]) (by norm_num [coarseEnvelope])).trans
  norm_num [intermediatePairBudget, coarseEnvelope, pairMatrix64, vec_six_last]

private theorem displayed_slopes_nonneg (i : Fin 41) :
    0 ≤ (displayedRows i).c ∧ 0 ≤ (displayedRows i).g := by
  fin_cases i <;> norm_num [displayedRows]

private theorem displayed_budget_le (i : Fin 41) :
    intermediatePairBudget (displayedRows i) ≤
      8 * (4 * displayedScale i) * pairMatrix64 5 (displayedColor i) / 64 := by
  fin_cases i <;>
    norm_num [intermediatePairBudget, displayedRows, displayedScale, displayedColor,
      pairMatrix64, vec_six_last, vec_six_two, vec_six_three, vec_six_four]

/-- Every literal displayed partner is checked with its original scale
and color. This is a numerical statement, not catalogue coverage. -/
theorem displayed_cross_le_color_five (i : Fin 41) :
    intermediateEnvelope.symmetricSupport (displayedRows i) ≤
      8 * (4 * displayedScale i) * pairMatrix64 5 (displayedColor i) / 64 :=
  (symmetricSupport_le_budget (displayedRows i) (displayed_slopes_nonneg i).1
    (displayed_slopes_nonneg i).2).trans (displayed_budget_le i)

theorem bounded_cross_le_color_five (r : JointCapacityRow)
    (hr : r.BoundedBy intermediateEnvelope) (i : Fin 41) :
    r.symmetricSupport (displayedRows i) ≤
      8 * (4 * displayedScale i) * pairMatrix64 5 (displayedColor i) / 64 :=
  (JointCapacityRow.symmetricSupport_mono (s := displayedRows i) (S := displayedRows i) hr
    ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩).trans
      (displayed_cross_le_color_five i)

theorem bounded_pair_le_color_five (r s : JointCapacityRow)
    (hr : r.BoundedBy intermediateEnvelope) (hs : s.BoundedBy intermediateEnvelope) :
    r.symmetricSupport s ≤ 8 * 8 * pairMatrix64 5 5 / 64 :=
  (JointCapacityRow.symmetricSupport_mono hr hs).trans self_le_color_five

theorem bounded_coarse_pair_le_color_five (r s : JointCapacityRow)
    (hr : r.BoundedBy intermediateEnvelope) (hs : s.BoundedBy coarseEnvelope) :
    r.symmetricSupport s ≤ 8 * 8 * pairMatrix64 5 5 / 64 :=
  (JointCapacityRow.symmetricSupport_mono hr hs).trans coarse_cross_le_color_five

end SymmetricSubgroupAsymptotics.BinaryCarrierStarIntermediateEnvelope
