import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow11ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow11ModuleOrbitsChunk0

/-! Selected row 11 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow11ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow11ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop8TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow11ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 217) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow11ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 217
  · let j : Fin 217 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow11ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow11ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow11ModuleOrbitsChunk0.minimal j g
  omega

private theorem stabilizer_card (i : Fin 217) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow11ModuleRepresentation.representation (PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow11ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 217
  · let j : Fin 217 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow11ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow11ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow11ModuleOrbitsChunk0.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow11ModuleRepresentation.representation PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow11ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow11ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 217) :
    (PrimitiveAffineEightFrameRow11ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow11ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow11ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow11ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 217
  · let j : Fin 217 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow11ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow11ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow11ModuleOrbitsChunk0.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 217) :
    PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow11ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow11ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow11ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow11ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow11ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 217) :
    PrimitiveAffineEightFrameRow11ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow11ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 217
  · let j : Fin 217 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow11ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow11ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow11ModuleOrbitsChunk0.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 217) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow11ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow11ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow11ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow11ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow11ModuleRepresentation.states (PrimitiveAffineEightFrameRow11ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow11ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow11ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow11ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow11ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow11ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow11ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow11ModuleOrbits

end
