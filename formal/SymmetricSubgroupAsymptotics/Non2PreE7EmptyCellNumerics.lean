import SymmetricSubgroupAsymptotics.Non2PreE7CharacterCertificateTemplate
import SymmetricSubgroupAsymptotics.Non2PreE7NonPairPhysicalFrontier

/-!
# Numerically valid empty cells in the pre-E7 catalogue

The first-owner catalogue contains an entry for every owner label and every
literal action class.  When an action does not belong to a displayed owner,
the corresponding physical family is empty.  Its coefficients are therefore
zero, but its hot/cold parameters must still satisfy the global parameter
record: that record is quantified over every menu index, including empty
ones.

This file supplies one uniform harmless choice.  Every non-2 transitive
action has width at least three.  At such a width, degree one and margin
`rho*w/2` satisfy the complete parameter window at `rho = 1/8192`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- A non-2 transitive permutation action has at least three points. -/
theorem preE7NonPairAction_width_three_le
    {w : ℕ} (_i : PreE7NonPairActionClass w) : 3 ≤ w := by
  by_contra hw
  have hw' : w ≤ 2 := by omega
  have htop : IsPGroup 2 (Equiv.Perm (Fin w)) := by
    interval_cases w
    · apply IsPGroup.of_card (n := 0)
      simp
    · apply IsPGroup.of_card (n := 0)
      simp
    · apply IsPGroup.of_card (n := 1)
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      norm_num
  exact _i.1.1.representative_not_isPGroup
    (htop.to_subgroup (preE7NonPairAction w _i))

/-- Degree used by a catalogue cell whose physical family is empty.  Width
three is the sole place where a two-point seed would consume the whole even
width; all larger widths use the standard padded seed. -/
def preE7EmptyCellDegree (w : ℕ) : ℕ :=
  if w = 3 then 1 else paddedComparatorDegree preE7CharacterRho 2 w

/-- Positive margin used by an empty cell. -/
def preE7EmptyCellDelta (w : ℕ) : ℝ :=
  if w = 3 then preE7CharacterRho * w / 2
  else paddedComparatorDelta preE7CharacterRho 0 2 w

/-- Threshold attached to the empty cell's degree and margin. -/
def preE7EmptyCellCutoff (w : ℕ) : ℝ :=
  (preE7EmptyCellDegree w : ℝ) / 8 + preE7EmptyCellDelta w / 2

/-- The cold exponent of the empty cell. -/
def preE7EmptyCellAlpha (w : ℕ) : ℝ := preE7EmptyCellCutoff w

/-- Empty cells satisfy every global parameter inequality, including the
tail inequality, despite contributing no main or tail coefficient. -/
theorem preE7EmptyCell_entryParameters {w : ℕ} (hw : 3 ≤ w) :
    PreE7CharacterEntryParameters preE7CharacterRho w
      (preE7EmptyCellDegree w) 0 (preE7EmptyCellDelta w)
      (preE7EmptyCellCutoff w) (preE7EmptyCellAlpha w) 0 := by
  by_cases h3 : w = 3
  · subst w
    refine
      { delta_nonneg := by
          norm_num [preE7CharacterRho, preE7EmptyCellDelta]
        degree_pos := by norm_num [preE7EmptyCellDegree]
        ratio := by
          norm_num [preE7CharacterRho, preE7EmptyCellDegree,
            preE7EmptyCellDelta]
        degree_upper := by
          norm_num [preE7CharacterRho, preE7EmptyCellDegree]
        delta_lower := by
          norm_num [preE7CharacterRho, preE7EmptyCellDelta]
        hot_margin := by
          norm_num [preE7CharacterRho, preE7EmptyCellDegree,
            preE7EmptyCellDelta, preE7EmptyCellCutoff]
        threshold_eq := rfl
        delta_upper := by
          norm_num [preE7CharacterRho, preE7EmptyCellDelta]
        degree_lower := by
          norm_num [preE7CharacterRho, preE7EmptyCellDegree]
        degree_width := by norm_num [preE7EmptyCellDegree]
        cold_slope := by simp [preE7EmptyCellAlpha]
        cold_gap := by
          norm_num [preE7CharacterRho, preE7EmptyCellDegree,
            preE7EmptyCellDelta, preE7EmptyCellCutoff,
            preE7EmptyCellAlpha, halfDegree]
        tail_gap := by norm_num [preE7CharacterRho, halfDegree] }
  · have hw4 : 4 ≤ w := by omega
    have hwR : (4 : ℝ) ≤ w := by exact_mod_cast hw4
    have hevenLower0 : (w : ℝ) ≤ (evenWidth w : ℝ) + 1 := by
      exact_mod_cast width_le_evenWidth_add_one w
    have hevenLower : (w : ℝ) - 1 ≤ (evenWidth w : ℝ) := by
      linarith
    have hmargin : preE7CharacterRho * w ≤
        ((evenWidth w : ℝ) - 2) / 8 := by
      unfold preE7CharacterRho
      norm_num
      linarith
    let idx : ℕ → Type := fun w' => {_u : Unit // w' = w}
    have hP := growingPadded_parameterBound (ι := idx)
      (ρ := preE7CharacterRho) (fun _ _ => 2) (fun _ _ => 0)
      (by norm_num [preE7CharacterRho])
      (by norm_num [preE7CharacterRho])
      (fun _ _ => le_rfl) (fun _ _ => by norm_num)
      (by
        rintro w' ⟨_, rfl⟩
        simpa using hmargin)
    let j : idx w := ⟨(), rfl⟩
    have hp : PreE7CharacterEntryParameters preE7CharacterRho w
        (paddedComparatorDegree preE7CharacterRho 2 w) 0
        (paddedComparatorDelta preE7CharacterRho 0 2 w)
        ((paddedComparatorDegree preE7CharacterRho 2 w : ℝ) / 8 +
          paddedComparatorDelta preE7CharacterRho 0 2 w / 2)
        (0 + ((paddedComparatorDegree preE7CharacterRho 2 w : ℝ) / 8 +
          paddedComparatorDelta preE7CharacterRho 0 2 w / 2)) 0 :=
      { delta_nonneg := hP.delta_nonneg w j
        degree_pos := hP.degree_pos w j
        ratio := hP.ratio w j
        degree_upper := hP.degree_upper w j
        delta_lower := hP.delta_lower w j
        hot_margin := hP.hot_margin w j
        threshold_eq := hP.threshold_eq w j
        delta_upper := hP.delta_upper w j
        degree_lower := hP.degree_lower w j
        degree_width := hP.degree_width w j
        cold_slope := hP.cold_slope w j
        cold_gap := hP.cold_gap w j
        tail_gap := by
          have hhalf : (evenWidth w : ℝ) = 2 * halfDegree w := by
            exact_mod_cast (show evenWidth w = 2 * halfDegree w by rfl)
          unfold preE7CharacterRho
          norm_num
          linarith [hevenLower] }
    simpa [preE7EmptyCellDegree, h3, preE7EmptyCellDelta,
      preE7EmptyCellCutoff, preE7EmptyCellAlpha,
      paddedComparatorDelta, preE7CharacterRho] using hp

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
