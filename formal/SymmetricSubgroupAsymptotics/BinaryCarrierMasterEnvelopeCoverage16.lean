import SymmetricSubgroupAsymptotics.BinaryCarrierMasterMenu
import SymmetricSubgroupAsymptotics.BinaryCarrierPairNormalRows16
import SymmetricSubgroupAsymptotics.BinaryCarrierStarNormalRows16T1332

/-! Every original normal axis in each of the five literal masters has
an effective upper envelope in the shared fourteen-label menu. The
original subgroup order is retained: only its feasible polygon budget is
compared with the envelope. Multiple axes may receive the same label;
no count, sum of weights, owner assertion or global recurrence follows. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open FullSubdirectGoursat JointCapacityRow BinaryCarrierMasterMenu
open BinaryCarrierMasterEnvelopes

private theorem masterMenu_of_h16 (r : JointCapacityRow) (i : Fin 12)
    (h : r.EffectivelyBoundedBy (h16 i)) :
    ∃ label : Label, r.EffectivelyBoundedBy (envelope label) :=
  ⟨h16Label i, by simpa only [envelope_h16] using h⟩

private theorem masterMenu_above_pair_four (r : JointCapacityRow) (w : ℕ) (hw : w ≤ 6)
    (h : r.BoundedBy (BinaryCarrierAboveDerivedRows.row 4 6 3 w)) :
    ∃ label : Label, r.EffectivelyBoundedBy (envelope label) := by
  let i : Fin 7 := ⟨w, by omega⟩
  exact masterMenu_of_h16 r (pairFourTarget i) (h.effective.trans (above_pair_four i))

private theorem masterMenu_above_pair_six (r : JointCapacityRow) (w : ℕ) (hw : w ≤ 6)
    (h : r.BoundedBy (BinaryCarrierAboveDerivedRows.row 6 6 3 w)) :
    ∃ label : Label, r.EffectivelyBoundedBy (envelope label) := by
  let i : Fin 7 := ⟨w, by omega⟩
  exact masterMenu_of_h16 r (pairSixTarget i) (h.effective.trans (above_pair_six i))

private theorem masterMenu_above_star (r : JointCapacityRow) (w : ℕ) (hw : w ≤ 5)
    (h : r.BoundedBy (BinaryCarrierAboveDerivedRows.row 6 5 4 w)) :
    ∃ label : Label, r.EffectivelyBoundedBy (envelope label) := by
  let i : Fin 6 := ⟨w, by omega⟩
  exact masterMenu_of_h16 r (starTarget i) (h.effective.trans (above_star i))

private theorem masterMenu_pair_crossing (b w : ℕ) (hw1 : 1 ≤ w) (hw2 : w ≤ 2) :
    ∃ label : Label,
      (BinaryCarrierCrossingRows.row b w).EffectivelyBoundedBy (envelope label) :=
  masterMenu_of_h16 _ 4 (pair_crossing_of_bounds b w hw1 hw2)

namespace BinaryCarrierMasterEnvelopeCoverage16T1082

abbrev Original := BinaryCarrierPairNormalRows16T1082.Original
abbrev factor := BinaryCarrierPairNormalRows16T1082.factor

theorem actualRow_effectivelyBoundedBy_envelope (N : NormalAxis Original) :
    ∃ label : Label,
      (BinaryCarrierWord.actualRow (A := factor) N).EffectivelyBoundedBy (envelope label) := by
  rcases BinaryCarrierPairNormalRows16T1082.actualRow_coverage N with h | h | h | h
  · exact masterMenu_above_pair_four _ _ h.2.1 h.2.2
  · rcases h.2 with h | h
    · rw [h]
      exact masterMenu_of_h16 _ 0 pair_small_bottom
    · rw [h]
      exact masterMenu_of_h16 _ 2 pair_small_radical
  · rcases h.2.2 with h | h
    · rw [h]
      exact masterMenu_of_h16 _ 2 pair_intermediate_one
    · rw [h]
      exact masterMenu_of_h16 _ 3 pair_intermediate_two
  · rcases h.2.2 with h | h
    · rw [h]
      exact masterMenu_pair_crossing 3 1 (by decide) (by decide)
    · rw [h]
      exact masterMenu_pair_crossing 3 2 (by decide) (by decide)

end BinaryCarrierMasterEnvelopeCoverage16T1082

namespace BinaryCarrierMasterEnvelopeCoverage16T1083

abbrev Original := BinaryCarrierPairNormalRows16T1083.Original
abbrev factor := BinaryCarrierPairNormalRows16T1083.factor

theorem actualRow_effectivelyBoundedBy_envelope (N : NormalAxis Original) :
    ∃ label : Label,
      (BinaryCarrierWord.actualRow (A := factor) N).EffectivelyBoundedBy (envelope label) := by
  rcases BinaryCarrierPairNormalRows16T1083.actualRow_coverage N with h | h | h | h
  · exact masterMenu_above_pair_four _ _ h.2.1 h.2.2
  · rcases h.2 with h | h
    · rw [h]
      exact masterMenu_of_h16 _ 0 pair_small_bottom
    · rw [h]
      exact masterMenu_of_h16 _ 2 pair_small_radical
  · rcases h.2.2 with h | h
    · rw [h]
      exact masterMenu_of_h16 _ 2 pair_intermediate_one
    · rw [h]
      exact masterMenu_of_h16 _ 3 pair_intermediate_two
  · rcases h.2.2 with h | h
    · rw [h]
      exact masterMenu_pair_crossing 3 1 (by decide) (by decide)
    · rw [h]
      exact masterMenu_pair_crossing 3 2 (by decide) (by decide)

end BinaryCarrierMasterEnvelopeCoverage16T1083

namespace BinaryCarrierMasterEnvelopeCoverage16T1084

abbrev Original := BinaryCarrierPairNormalRows16T1084.Original
abbrev factor := BinaryCarrierPairNormalRows16T1084.factor

theorem actualRow_effectivelyBoundedBy_envelope (N : NormalAxis Original) :
    ∃ label : Label,
      (BinaryCarrierWord.actualRow (A := factor) N).EffectivelyBoundedBy (envelope label) := by
  rcases BinaryCarrierPairNormalRows16T1084.actualRow_coverage N with h | h | h | h
  · exact masterMenu_above_pair_four _ _ h.2.1 h.2.2
  · rcases h.2 with h | h
    · rw [h]
      exact masterMenu_of_h16 _ 0 pair_small_bottom
    · rw [h]
      exact masterMenu_of_h16 _ 2 pair_small_radical
  · rcases h.2.2 with h | h
    · rw [h]
      exact masterMenu_of_h16 _ 2 pair_intermediate_one
    · rw [h]
      exact masterMenu_of_h16 _ 3 pair_intermediate_two
  · rcases h.2.2 with h | h
    · rw [h]
      exact masterMenu_pair_crossing 3 1 (by decide) (by decide)
    · rw [h]
      exact masterMenu_pair_crossing 3 2 (by decide) (by decide)

end BinaryCarrierMasterEnvelopeCoverage16T1084

namespace BinaryCarrierMasterEnvelopeCoverage16T1332

abbrev Original := BinaryCarrierStarNormalRows16T1332.Original
abbrev factor := BinaryCarrierStarNormalRows16T1332.factor

theorem actualRow_effectivelyBoundedBy_envelope (N : NormalAxis Original) :
    ∃ label : Label,
      (BinaryCarrierWord.actualRow (A := factor) N).EffectivelyBoundedBy (envelope label) := by
  rcases BinaryCarrierStarNormalRows16T1332.actualRow_coverage N with h | h | h | h
  · exact masterMenu_above_star _ _ h.2.1 h.2.2
  · rcases h.2 with h | h | h
    · rw [h]
      exact masterMenu_of_h16 _ 0 star_small_bottom
    · rw [h]
      exact masterMenu_of_h16 _ 1 star_small_one
    · rw [h]
      exact masterMenu_of_h16 _ 2 star_small_radical
  · rcases h.2.2 with h | h | h
    · rw [h]
      exact masterMenu_of_h16 _ 2 star_intermediate_one
    · rw [h]
      exact masterMenu_of_h16 _ 4 star_intermediate_two
    · refine ⟨starIntermediateLabel, ?_⟩
      rw [envelope_starIntermediate, h]
      exact EffectivelyBoundedBy.refl _
  · refine ⟨starCrossingLabel, ?_⟩
    simpa only [envelope_starCrossing] using h.2.2.effective

end BinaryCarrierMasterEnvelopeCoverage16T1332

namespace BinaryCarrierMasterEnvelopeCoverage16T1547

abbrev Original := BinaryCarrierPairNormalRows16T1547.Original
abbrev factor := BinaryCarrierPairNormalRows16T1547.factor

theorem actualRow_effectivelyBoundedBy_envelope (N : NormalAxis Original) :
    ∃ label : Label,
      (BinaryCarrierWord.actualRow (A := factor) N).EffectivelyBoundedBy (envelope label) := by
  rcases BinaryCarrierPairNormalRows16T1547.actualRow_coverage N with h | h | h | h
  · exact masterMenu_above_pair_six _ _ h.2.1 h.2.2
  · rcases h.2 with h | h | h | h
    · rw [h]
      exact masterMenu_of_h16 _ 0 large_pair_small_bottom
    · rw [h]
      exact masterMenu_of_h16 _ 1 large_pair_small_one
    · rw [h]
      exact masterMenu_of_h16 _ 2 large_pair_small_two
    · rw [h]
      exact masterMenu_of_h16 _ 3 large_pair_small_radical
  · rcases h.2.2 with h | h
    · rw [h]
      exact masterMenu_of_h16 _ 4 large_pair_intermediate_one
    · rw [h]
      exact masterMenu_of_h16 _ 4 large_pair_intermediate_two
  · rcases h.2.2 with h | h
    · rw [h]
      exact masterMenu_pair_crossing 5 1 (by decide) (by decide)
    · rw [h]
      exact masterMenu_pair_crossing 5 2 (by decide) (by decide)

end BinaryCarrierMasterEnvelopeCoverage16T1547

end SymmetricSubgroupAsymptotics
