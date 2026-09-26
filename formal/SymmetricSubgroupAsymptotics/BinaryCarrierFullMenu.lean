import SymmetricSubgroupAsymptotics.BinaryCarrierStarIntermediateEnvelope

/-! The 41 original displayed rows and two additional star envelopes.
Displayed labels retain their original scale and order. This finite scalar
menu does not identify, count, or weight any actual normal subgroup. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierFullMenu

abbrev Label := Fin 43

def displayedLabel (i : Fin 41) : Label := ⟨i.val, by omega⟩
def starCrossingLabel : Label := 41
def starIntermediateLabel : Label := 42

def envelope (i : Label) : JointCapacityRow :=
  if hi : i.val < 41 then BinaryCarrierStarEnvelope.displayedRows ⟨i.val, hi⟩ else
  if i.val = 41 then BinaryCarrierStarEnvelope.coarseEnvelope else
  BinaryCarrierStarIntermediateEnvelope.intermediateEnvelope

/-- Scale one is retained on the original degree-eight displayed rows;
the twelve H16 rows and two extra star envelopes retain scale two. -/
def physicalScale (i : Label) : ℝ :=
  if hi : i.val < 41 then BinaryCarrierStarEnvelope.displayedScale ⟨i.val, hi⟩ else 2

@[simp] theorem envelope_displayed (i : Fin 41) :
    envelope (displayedLabel i) = BinaryCarrierStarEnvelope.displayedRows i := by
  simp [envelope, displayedLabel, i.isLt]

@[simp] theorem envelope_starCrossing :
    envelope starCrossingLabel = BinaryCarrierStarEnvelope.coarseEnvelope := rfl

@[simp] theorem envelope_starIntermediate :
    envelope starIntermediateLabel =
      BinaryCarrierStarIntermediateEnvelope.intermediateEnvelope := rfl

@[simp] theorem physicalScale_displayed (i : Fin 41) :
    physicalScale (displayedLabel i) = BinaryCarrierStarEnvelope.displayedScale i := by
  simp [physicalScale, displayedLabel, i.isLt]

@[simp] theorem physicalScale_starCrossing : physicalScale starCrossingLabel = 2 := rfl
@[simp] theorem physicalScale_starIntermediate : physicalScale starIntermediateLabel = 2 := rfl

theorem label_cases (i : Label) :
    (∃ j : Fin 41, i = displayedLabel j) ∨
      i = starCrossingLabel ∨ i = starIntermediateLabel := by
  by_cases hi : i.val < 41
  · exact Or.inl ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
  · apply Or.inr
    by_cases h41 : i.val = 41
    · exact Or.inl (Fin.ext h41)
    · apply Or.inr
      apply Fin.ext
      change i.val = 42
      omega

theorem physicalScale_eq_one_or_two (i : Label) :
    physicalScale i = 1 ∨ physicalScale i = 2 := by
  rcases label_cases i with ⟨j, rfl⟩ | rfl | rfl
  · rw [physicalScale_displayed]
    unfold BinaryCarrierStarEnvelope.displayedScale
    split_ifs <;> simp
  · exact Or.inr physicalScale_starCrossing
  · exact Or.inr physicalScale_starIntermediate

theorem physicalScale_pos (i : Label) : 0 < physicalScale i := by
  rcases physicalScale_eq_one_or_two i with h | h <;> rw [h] <;> norm_num

end SymmetricSubgroupAsymptotics.BinaryCarrierFullMenu
