import SymmetricSubgroupAsymptotics.JointCapacityRowEnvelope
import SymmetricSubgroupAsymptotics.BinaryCarrierConeData

/-! A pure scalar certificate for the coarse star crossing envelope.
The 41 rows below are the displayed H16, X, J, P rows, in that order,
from paper/sections/carrier_cones.tex. Their colors are the displayed
domination colors after merging X_whole and P_whole. This module proves
only numerical inequalities against these literal rows. It does not
assert that an actual normal subgroup belongs to this menu. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierStarEnvelope

open BinaryCarrierCone

private theorem vec_six_last {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

private theorem vec_six_two {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (2 : Fin 6) = c := rfl

private theorem vec_six_three {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (3 : Fin 6) = d := rfl

private theorem vec_six_four {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (4 : Fin 6) = e := rfl

def coarseEnvelope : JointCapacityRow := ⟨3, 8, 3, 3, 3, 3⟩

/-- The original displayed block order is H16[0..11], X[0..8],
J[0..9], P[0..9]. No groups or normal-subgroup identifiers are assigned. -/
def displayedRows : Fin 41 → JointCapacityRow :=
  ![⟨0,0,0,0,1,6⟩, ⟨1,1,1,1,2,5⟩, ⟨1,2,1,1,4,4⟩,
    ⟨2,3,2,2,3,3⟩, ⟨2,4,2,2,4,2⟩, ⟨3,6,3,3,6,0⟩,
    ⟨4,6,4,4,5,0⟩, ⟨4,7,4,4,4,0⟩, ⟨4,8,4,4,3,0⟩,
    ⟨5,11,3,3,1,0⟩, ⟨5,11,4,4,0,0⟩, ⟨6,12,3,3,0,0⟩,
    ⟨0,0,0,0,1,3⟩, ⟨1,1,1,0,2,2⟩, ⟨1,2,1,1,2,1⟩,
    ⟨1,3,1,1,1,1⟩, ⟨1,4,2,2,2,0⟩, ⟨2,3,2,1,3,0⟩,
    ⟨2,4,2,1,2,0⟩, ⟨2,5,2,2,1,0⟩, ⟨3,6,2,2,0,0⟩,
    ⟨0,0,0,0,1,3⟩, ⟨1,1,1,0,1,2⟩, ⟨1,2,1,1,2,1⟩,
    ⟨1,3,1,1,1,1⟩, ⟨1,3,1,1,3,0⟩, ⟨1,4,1,1,2,0⟩,
    ⟨1,5,1,2,1,0⟩, ⟨2,4,1,1,2,0⟩, ⟨2,5,1,1,1,0⟩,
    ⟨2,6,1,2,0,0⟩,
    ⟨0,0,0,0,1,4⟩, ⟨1,1,1,0,1,3⟩, ⟨1,2,1,1,2,2⟩,
    ⟨1,3,1,1,2,1⟩, ⟨1,4,1,1,1,1⟩, ⟨1,5,2,2,2,0⟩,
    ⟨2,4,2,1,3,0⟩, ⟨2,5,2,1,2,0⟩, ⟨2,6,2,2,1,0⟩,
    ⟨3,7,2,2,0,0⟩]

def displayedScale (i : Fin 41) : ℝ := if i.val < 12 then 2 else 1

def displayedColor : Fin 41 → Fin 6 :=
  ![2,3,4,4,4,5,5,5,5,0,1,1,
    2,4,4,4,5,5,5,5,1,
    2,3,4,4,4,4,5,5,5,1,
    2,3,4,4,4,5,5,5,5,1]

/-- The first term bounds the support of the other row at (3,3).
The second bounds the coarse rectangle at its actual two slopes. -/
def envelopePairBudget (r : JointCapacityRow) : ℝ :=
  max (3 * min (r.n : ℝ) ((r.k : ℝ) + r.m)) (3 * (r.c + r.g))

theorem symmetricSupport_le_budget (r : JointCapacityRow)
    (hc : 0 ≤ r.c) (hg : 0 ≤ r.g) :
    coarseEnvelope.symmetricSupport r ≤ envelopePairBudget r := by
  have hfirst : coarseEnvelope.directedSupport r ≤
      3 * min (r.n : ℝ) ((r.k : ℝ) + r.m) := by
    apply jointCapacitySupport_le
    intro δ ε hδ hε hsum
    have hd : (δ : ℝ) ≤ r.k := Nat.cast_le.mpr hδ
    have he : (ε : ℝ) ≤ r.m := Nat.cast_le.mpr hε
    have hn : (δ : ℝ) + ε ≤ r.n := by exact_mod_cast hsum
    have hmin : (δ : ℝ) + ε ≤ min (r.n : ℝ) ((r.k : ℝ) + r.m) :=
      le_min hn (add_le_add hd he)
    change 3 * (δ : ℝ) + 3 * ε ≤ _
    linarith
  have hsecond : r.directedSupport coarseEnvelope ≤ 3 * (r.c + r.g) := by
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

theorem head_le_color_five : (coarseEnvelope.k : ℝ) ≤ 8 * alpha 5 := by
  norm_num [coarseEnvelope, alpha, vec_six_last]

theorem second_le_color_five :
    ((max coarseEnvelope.m coarseEnvelope.a₂ : ℕ) : ℝ) ≤ 8 * beta 5 := by
  norm_num [coarseEnvelope, beta, vec_six_last]

theorem self_le_color_five :
    coarseEnvelope.symmetricSupport coarseEnvelope ≤ 8 * 8 * pairMatrix64 5 5 / 64 := by
  apply (symmetricSupport_le_budget coarseEnvelope (by norm_num [coarseEnvelope])
    (by norm_num [coarseEnvelope])).trans
  norm_num [envelopePairBudget, coarseEnvelope, pairMatrix64, vec_six_last]

private theorem displayed_slopes_nonneg (i : Fin 41) :
    0 ≤ (displayedRows i).c ∧ 0 ≤ (displayedRows i).g := by
  fin_cases i <;> norm_num [displayedRows]

private theorem displayed_budget_le (i : Fin 41) :
    envelopePairBudget (displayedRows i) ≤
      8 * (4 * displayedScale i) * pairMatrix64 5 (displayedColor i) / 64 := by
  fin_cases i <;>
    norm_num [envelopePairBudget, displayedRows, displayedScale, displayedColor, pairMatrix64,
      vec_six_last, vec_six_two, vec_six_three, vec_six_four]

/-- Every original displayed cross column is checked, including the
degree-eight columns. The physical masses are 8 and 4 times its scale. -/
theorem displayed_cross_le_color_five (i : Fin 41) :
    coarseEnvelope.symmetricSupport (displayedRows i) ≤
      8 * (4 * displayedScale i) * pairMatrix64 5 (displayedColor i) / 64 :=
  (symmetricSupport_le_budget (displayedRows i) (displayed_slopes_nonneg i).1
    (displayed_slopes_nonneg i).2).trans (displayed_budget_le i)

theorem bounded_cross_le_color_five (r : JointCapacityRow)
    (hr : r.BoundedBy coarseEnvelope) (i : Fin 41) :
    r.symmetricSupport (displayedRows i) ≤
      8 * (4 * displayedScale i) * pairMatrix64 5 (displayedColor i) / 64 :=
  (JointCapacityRow.symmetricSupport_mono (s := displayedRows i) (S := displayedRows i) hr
    ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩).trans
      (displayed_cross_le_color_five i)

theorem bounded_pair_le_color_five (r s : JointCapacityRow)
    (hr : r.BoundedBy coarseEnvelope) (hs : s.BoundedBy coarseEnvelope) :
    r.symmetricSupport s ≤ 8 * 8 * pairMatrix64 5 5 / 64 :=
  (JointCapacityRow.symmetricSupport_mono hr hs).trans self_le_color_five

end SymmetricSubgroupAsymptotics.BinaryCarrierStarEnvelope
