import SymmetricSubgroupAsymptotics.BinaryCarrierFullMenu
import SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairs

/-! Head, second-mark and all ordered-pair energy bounds for the 43-label
scalar menu. Each displayed label keeps its own physical mass four or
eight; both additional star labels have mass eight and color five.
No actual subgroup coverage, multiplicity, or weight is supplied here. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierFullMenuEnergy

open BinaryCarrierFullMenu BinaryCarrierCone

def color (i : Label) : Fin 6 :=
  if hi : i.val < 41 then BinaryCarrierStarEnvelope.displayedColor ⟨i.val, hi⟩ else 5

def mass (i : Label) : ℝ := 4 * physicalScale i

theorem mass_eq_physicalScale (i : Label) : mass i = 4 * physicalScale i := rfl

@[simp] theorem color_displayed (i : Fin 41) :
    color (displayedLabel i) = BinaryCarrierStarEnvelope.displayedColor i := by
  simp [color, displayedLabel, i.isLt]

@[simp] theorem color_starCrossing : color starCrossingLabel = 5 := rfl
@[simp] theorem color_starIntermediate : color starIntermediateLabel = 5 := rfl

@[simp] theorem mass_displayed (i : Fin 41) :
    mass (displayedLabel i) = 4 * BinaryCarrierStarEnvelope.displayedScale i := by
  rw [mass, physicalScale_displayed]

@[simp] theorem mass_starCrossing : mass starCrossingLabel = 8 := by
  norm_num [mass]

@[simp] theorem mass_starIntermediate : mass starIntermediateLabel = 8 := by
  norm_num [mass]

theorem mass_pos (i : Label) : 0 < mass i :=
  mul_pos (by norm_num : (0 : ℝ) < 4) (physicalScale_pos i)

theorem mass_nonneg (i : Label) : 0 ≤ mass i := (mass_pos i).le

theorem mass_eq_four_or_eight (i : Label) : mass i = 4 ∨ mass i = 8 := by
  rcases physicalScale_eq_one_or_two i with h | h
  · left
    norm_num [mass, h]
  · right
    norm_num [mass, h]

theorem head_le (i : Label) : ((envelope i).k : ℝ) ≤ mass i * alpha (color i) := by
  rcases label_cases i with ⟨j, rfl⟩ | rfl | rfl
  · simpa only [envelope_displayed, mass_displayed, color_displayed] using
      BinaryCarrierDisplayedPairs.displayed_head_le j
  · simpa only [envelope_starCrossing, mass_starCrossing, color_starCrossing] using
      BinaryCarrierStarEnvelope.head_le_color_five
  · simpa only [envelope_starIntermediate, mass_starIntermediate, color_starIntermediate] using
      BinaryCarrierStarIntermediateEnvelope.head_le_color_five

theorem second_le (i : Label) :
    ((max (envelope i).m (envelope i).a₂ : ℕ) : ℝ) ≤ mass i * beta (color i) := by
  rcases label_cases i with ⟨j, rfl⟩ | rfl | rfl
  · simpa only [envelope_displayed, mass_displayed, color_displayed] using
      BinaryCarrierDisplayedPairs.displayed_second_le j
  · simpa only [envelope_starCrossing, mass_starCrossing, color_starCrossing] using
      BinaryCarrierStarEnvelope.second_le_color_five
  · simpa only [envelope_starIntermediate, mass_starIntermediate, color_starIntermediate] using
      BinaryCarrierStarIntermediateEnvelope.second_le_color_five

private theorem matrix_symmetric (c d : Fin 6) :
    pairMatrix64 c d = pairMatrix64 d c := by
  fin_cases c <;> fin_cases d <;> rfl

private theorem displayed_pair (i j : Fin 41) :
    (envelope (displayedLabel i)).symmetricSupport (envelope (displayedLabel j)) ≤
      mass (displayedLabel i) * mass (displayedLabel j) *
        pairMatrix64 (color (displayedLabel i)) (color (displayedLabel j)) / 64 := by
  simpa only [envelope_displayed, mass_displayed, color_displayed] using
    BinaryCarrierDisplayedPairs.displayed_pair_le i j

private theorem crossing_displayed (i : Fin 41) :
    (envelope starCrossingLabel).symmetricSupport (envelope (displayedLabel i)) ≤
      mass starCrossingLabel * mass (displayedLabel i) *
        pairMatrix64 (color starCrossingLabel) (color (displayedLabel i)) / 64 := by
  simpa only [envelope_starCrossing, envelope_displayed, mass_starCrossing,
    mass_displayed, color_starCrossing, color_displayed] using
    BinaryCarrierStarEnvelope.displayed_cross_le_color_five i

private theorem intermediate_displayed (i : Fin 41) :
    (envelope starIntermediateLabel).symmetricSupport (envelope (displayedLabel i)) ≤
      mass starIntermediateLabel * mass (displayedLabel i) *
        pairMatrix64 (color starIntermediateLabel) (color (displayedLabel i)) / 64 := by
  simpa only [envelope_starIntermediate, envelope_displayed, mass_starIntermediate,
    mass_displayed, color_starIntermediate, color_displayed] using
    BinaryCarrierStarIntermediateEnvelope.displayed_cross_le_color_five i

private theorem crossing_self :
    (envelope starCrossingLabel).symmetricSupport (envelope starCrossingLabel) ≤
      mass starCrossingLabel * mass starCrossingLabel *
        pairMatrix64 (color starCrossingLabel) (color starCrossingLabel) / 64 := by
  simpa only [envelope_starCrossing, mass_starCrossing, color_starCrossing] using
    BinaryCarrierStarEnvelope.self_le_color_five

private theorem intermediate_self :
    (envelope starIntermediateLabel).symmetricSupport (envelope starIntermediateLabel) ≤
      mass starIntermediateLabel * mass starIntermediateLabel *
        pairMatrix64 (color starIntermediateLabel) (color starIntermediateLabel) / 64 := by
  simpa only [envelope_starIntermediate, mass_starIntermediate, color_starIntermediate] using
    BinaryCarrierStarIntermediateEnvelope.self_le_color_five

private theorem intermediate_crossing :
    (envelope starIntermediateLabel).symmetricSupport (envelope starCrossingLabel) ≤
      mass starIntermediateLabel * mass starCrossingLabel *
        pairMatrix64 (color starIntermediateLabel) (color starCrossingLabel) / 64 := by
  simpa only [envelope_starIntermediate, envelope_starCrossing,
    mass_starIntermediate, mass_starCrossing, color_starIntermediate, color_starCrossing] using
    BinaryCarrierStarIntermediateEnvelope.coarse_cross_le_color_five

private theorem pair_reverse {i j : Label}
    (h : (envelope i).symmetricSupport (envelope j) ≤
      mass i * mass j * pairMatrix64 (color i) (color j) / 64) :
    (envelope j).symmetricSupport (envelope i) ≤
      mass j * mass i * pairMatrix64 (color j) (color i) / 64 := by
  rw [JointCapacityRow.symmetricSupport_comm (envelope j) (envelope i),
    matrix_symmetric (color j) (color i), mul_comm (mass j) (mass i)]
  exact h

/-- All 1849 ordered pairs, including the original scale-one rows and
both orientations of their interactions with either star envelope. -/
theorem pair_le (i j : Label) :
    (envelope i).symmetricSupport (envelope j) ≤
      mass i * mass j * pairMatrix64 (color i) (color j) / 64 := by
  rcases label_cases i with ⟨a, rfl⟩ | rfl | rfl
  · rcases label_cases j with ⟨b, rfl⟩ | rfl | rfl
    · exact displayed_pair a b
    · exact pair_reverse (crossing_displayed a)
    · exact pair_reverse (intermediate_displayed a)
  · rcases label_cases j with ⟨b, rfl⟩ | rfl | rfl
    · exact crossing_displayed b
    · exact crossing_self
    · exact pair_reverse intermediate_crossing
  · rcases label_cases j with ⟨b, rfl⟩ | rfl | rfl
    · exact intermediate_displayed b
    · exact intermediate_crossing
    · exact intermediate_self

end SymmetricSubgroupAsymptotics.BinaryCarrierFullMenuEnergy
