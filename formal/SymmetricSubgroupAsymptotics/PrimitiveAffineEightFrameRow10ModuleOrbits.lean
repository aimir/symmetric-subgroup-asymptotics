import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow10ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow10ModuleOrbitsChunk0

/-! Selected row 10 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow10ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow10ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop8TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow10ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 217) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow10ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 217
  · let j : Fin 217 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow10ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow10ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow10ModuleOrbitsChunk0.minimal j g
  omega

private theorem stabilizer_card (i : Fin 217) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow10ModuleRepresentation.representation (PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow10ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 217
  · let j : Fin 217 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow10ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow10ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow10ModuleOrbitsChunk0.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow10ModuleRepresentation.representation PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow10ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow10ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 217) :
    (PrimitiveAffineEightFrameRow10ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow10ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow10ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow10ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 217
  · let j : Fin 217 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow10ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow10ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow10ModuleOrbitsChunk0.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 217) :
    PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow10ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow10ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow10ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow10ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow10ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 217) :
    PrimitiveAffineEightFrameRow10ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow10ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 217
  · let j : Fin 217 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow10ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow10ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow10ModuleOrbitsChunk0.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 217) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow10ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow10ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow10ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow10ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow10ModuleRepresentation.states (PrimitiveAffineEightFrameRow10ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow10ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow10ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow10ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow10ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow10ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow10ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow10ModuleOrbits

end
