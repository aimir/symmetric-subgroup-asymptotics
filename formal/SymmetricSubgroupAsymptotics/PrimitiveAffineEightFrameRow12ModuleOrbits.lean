import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleOrbitsChunk0

/-! Selected row 12 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow12ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop8TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow12ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 203) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow12ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 203
  · let j : Fin 203 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow12ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow12ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow12ModuleOrbitsChunk0.minimal j g
  omega

private theorem stabilizer_card (i : Fin 203) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow12ModuleRepresentation.representation (PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow12ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 203
  · let j : Fin 203 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow12ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow12ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow12ModuleOrbitsChunk0.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow12ModuleRepresentation.representation PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow12ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow12ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 203) :
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow12ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 203
  · let j : Fin 203 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow12ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow12ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow12ModuleOrbitsChunk0.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 203) :
    PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow12ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow12ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 203) :
    PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 203
  · let j : Fin 203 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow12ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow12ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow12ModuleOrbitsChunk0.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 203) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow12ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow12ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow12ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleOrbits

end
