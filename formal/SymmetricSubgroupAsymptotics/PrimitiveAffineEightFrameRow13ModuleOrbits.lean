import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleOrbitsChunk0

/-! Selected row 13 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow13ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop8TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow13ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 235) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow13ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 235
  · let j : Fin 235 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow13ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow13ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow13ModuleOrbitsChunk0.minimal j g
  omega

private theorem stabilizer_card (i : Fin 235) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow13ModuleRepresentation.representation (PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow13ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 235
  · let j : Fin 235 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow13ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow13ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow13ModuleOrbitsChunk0.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow13ModuleRepresentation.representation PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow13ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow13ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 235) :
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow13ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 235
  · let j : Fin 235 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow13ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow13ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow13ModuleOrbitsChunk0.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 235) :
    PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow13ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 235) :
    PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 235
  · let j : Fin 235 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow13ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow13ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow13ModuleOrbitsChunk0.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 235) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow13ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow13ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow13ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleOrbits

end
