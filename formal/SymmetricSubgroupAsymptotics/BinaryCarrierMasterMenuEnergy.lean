import SymmetricSubgroupAsymptotics.BinaryCarrierMasterMenu
import SymmetricSubgroupAsymptotics.BinaryCarrierStarIntermediateEnvelope
import SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairs

/-! Numerical energy certificates for the fourteen master-envelope labels.
Every label has physical mass eight. All pair comparisons include the two
additional star labels and retain the original displayed colors on H16.
This module concerns scalar labels only: it does not count original normal
subgroups or assign their individual weights. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierMasterMenuEnergy

open BinaryCarrierMasterMenu BinaryCarrierCone

def displayedIndex (i : Fin 12) : Fin 41 := ⟨i.val, by omega⟩

def color (i : Label) : Fin 6 :=
  if hi : i.val < 12 then
    BinaryCarrierStarEnvelope.displayedColor (displayedIndex ⟨i.val, hi⟩)
  else 5

def mass (_ : Label) : ℝ := 8

@[simp] theorem mass_eq (i : Label) : mass i = 8 := rfl

theorem mass_eq_physicalScale (i : Label) : mass i = 4 * physicalScale i := by
  norm_num [mass, physicalScale]

@[simp] theorem color_h16 (i : Fin 12) :
    color (h16Label i) = BinaryCarrierStarEnvelope.displayedColor (displayedIndex i) := by
  simp [color, h16Label, i.isLt]

@[simp] theorem color_starCrossing : color starCrossingLabel = 5 := rfl

@[simp] theorem color_starIntermediate : color starIntermediateLabel = 5 := rfl

private theorem envelope_h16_displayed (i : Fin 12) :
    envelope (h16Label i) = BinaryCarrierStarEnvelope.displayedRows (displayedIndex i) :=
  (envelope_h16 i).trans (BinaryCarrierMasterEnvelopes.h16_eq_displayed i)

private theorem displayedScale_h16 (i : Fin 12) :
    BinaryCarrierStarEnvelope.displayedScale (displayedIndex i) = 2 := by
  simp [BinaryCarrierStarEnvelope.displayedScale, displayedIndex, i.isLt]

private theorem envelope_intermediate :
    envelope starIntermediateLabel =
      BinaryCarrierStarIntermediateEnvelope.intermediateEnvelope := rfl

private theorem label_cases (i : Label) :
    (∃ j : Fin 12, i = h16Label j) ∨
      i = starCrossingLabel ∨ i = starIntermediateLabel := by
  by_cases hi : i.val < 12
  · exact Or.inl ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
  · apply Or.inr
    by_cases h12 : i.val = 12
    · exact Or.inl (Fin.ext h12)
    · apply Or.inr
      apply Fin.ext
      change i.val = 13
      omega

private theorem matrix_symmetric (c d : Fin 6) :
    pairMatrix64 c d = pairMatrix64 d c := by
  fin_cases c <;> fin_cases d <;> rfl

private theorem h16_head (i : Fin 12) :
    ((envelope (h16Label i)).k : ℝ) ≤ 8 * alpha (color (h16Label i)) := by
  rw [envelope_h16_displayed, color_h16]
  simpa only [displayedScale_h16, show (4 : ℝ) * 2 = 8 by norm_num] using
    BinaryCarrierDisplayedPairs.displayed_head_le (displayedIndex i)

private theorem h16_second (i : Fin 12) :
    ((max (envelope (h16Label i)).m (envelope (h16Label i)).a₂ : ℕ) : ℝ) ≤
      8 * beta (color (h16Label i)) := by
  rw [envelope_h16_displayed, color_h16]
  simpa only [displayedScale_h16, show (4 : ℝ) * 2 = 8 by norm_num] using
    BinaryCarrierDisplayedPairs.displayed_second_le (displayedIndex i)

theorem head_le (i : Label) : ((envelope i).k : ℝ) ≤ 8 * alpha (color i) := by
  rcases label_cases i with ⟨j, rfl⟩ | rfl | rfl
  · exact h16_head j
  · simpa only [envelope_starCrossing, color_starCrossing] using
      BinaryCarrierStarEnvelope.head_le_color_five
  · simpa only [envelope_intermediate, color_starIntermediate] using
      BinaryCarrierStarIntermediateEnvelope.head_le_color_five

theorem second_le (i : Label) :
    ((max (envelope i).m (envelope i).a₂ : ℕ) : ℝ) ≤ 8 * beta (color i) := by
  rcases label_cases i with ⟨j, rfl⟩ | rfl | rfl
  · exact h16_second j
  · simpa only [envelope_starCrossing, color_starCrossing] using
      BinaryCarrierStarEnvelope.second_le_color_five
  · simpa only [envelope_intermediate, color_starIntermediate] using
      BinaryCarrierStarIntermediateEnvelope.second_le_color_five

private theorem h16_pair (i j : Fin 12) :
    (envelope (h16Label i)).symmetricSupport (envelope (h16Label j)) ≤
      8 * 8 * pairMatrix64 (color (h16Label i)) (color (h16Label j)) / 64 := by
  rw [envelope_h16_displayed, envelope_h16_displayed, color_h16, color_h16]
  simpa only [displayedScale_h16, show (4 : ℝ) * 2 = 8 by norm_num] using
    BinaryCarrierDisplayedPairs.displayed_pair_le (displayedIndex i) (displayedIndex j)

private theorem crossing_h16 (i : Fin 12) :
    (envelope starCrossingLabel).symmetricSupport (envelope (h16Label i)) ≤
      8 * 8 * pairMatrix64 (color starCrossingLabel) (color (h16Label i)) / 64 := by
  rw [envelope_starCrossing, envelope_h16_displayed, color_starCrossing, color_h16]
  simpa only [displayedScale_h16, show (4 : ℝ) * 2 = 8 by norm_num] using
    BinaryCarrierStarEnvelope.displayed_cross_le_color_five (displayedIndex i)

private theorem intermediate_h16 (i : Fin 12) :
    (envelope starIntermediateLabel).symmetricSupport (envelope (h16Label i)) ≤
      8 * 8 * pairMatrix64 (color starIntermediateLabel) (color (h16Label i)) / 64 := by
  rw [envelope_intermediate, envelope_h16_displayed, color_starIntermediate, color_h16]
  simpa only [displayedScale_h16, show (4 : ℝ) * 2 = 8 by norm_num] using
    BinaryCarrierStarIntermediateEnvelope.displayed_cross_le_color_five (displayedIndex i)

private theorem crossing_self :
    (envelope starCrossingLabel).symmetricSupport (envelope starCrossingLabel) ≤
      8 * 8 * pairMatrix64 (color starCrossingLabel) (color starCrossingLabel) / 64 := by
  simpa only [envelope_starCrossing, color_starCrossing] using
    BinaryCarrierStarEnvelope.self_le_color_five

private theorem intermediate_self :
    (envelope starIntermediateLabel).symmetricSupport (envelope starIntermediateLabel) ≤
      8 * 8 * pairMatrix64 (color starIntermediateLabel) (color starIntermediateLabel) / 64 := by
  simpa only [envelope_intermediate, color_starIntermediate] using
    BinaryCarrierStarIntermediateEnvelope.self_le_color_five

private theorem intermediate_crossing :
    (envelope starIntermediateLabel).symmetricSupport (envelope starCrossingLabel) ≤
      8 * 8 * pairMatrix64 (color starIntermediateLabel) (color starCrossingLabel) / 64 := by
  simpa only [envelope_intermediate, envelope_starCrossing,
    color_starIntermediate, color_starCrossing] using
    BinaryCarrierStarIntermediateEnvelope.coarse_cross_le_color_five

private theorem pair_reverse {i j : Label}
    (h : (envelope i).symmetricSupport (envelope j) ≤
      8 * 8 * pairMatrix64 (color i) (color j) / 64) :
    (envelope j).symmetricSupport (envelope i) ≤
      8 * 8 * pairMatrix64 (color j) (color i) / 64 := by
  rw [JointCapacityRow.symmetricSupport_comm (envelope j) (envelope i),
    matrix_symmetric (color j) (color i)]
  exact h

/-- All 196 ordered pairs of scalar labels, including both orientations
of every pair involving either of the two additional star rows. -/
theorem pair_le (i j : Label) :
    (envelope i).symmetricSupport (envelope j) ≤
      8 * 8 * pairMatrix64 (color i) (color j) / 64 := by
  rcases label_cases i with ⟨a, rfl⟩ | rfl | rfl
  · rcases label_cases j with ⟨b, rfl⟩ | rfl | rfl
    · exact h16_pair a b
    · exact pair_reverse (crossing_h16 a)
    · exact pair_reverse (intermediate_h16 a)
  · rcases label_cases j with ⟨b, rfl⟩ | rfl | rfl
    · exact crossing_h16 b
    · exact crossing_self
    · exact pair_reverse intermediate_crossing
  · rcases label_cases j with ⟨b, rfl⟩ | rfl | rfl
    · exact intermediate_h16 b
    · exact intermediate_crossing
    · exact intermediate_self

end SymmetricSubgroupAsymptotics.BinaryCarrierMasterMenuEnergy
