import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleOrbitsChunk0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleOrbitsChunk256

/-! Selected row 6 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow6ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow6TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow6ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 342) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow6ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow6ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow6ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow6ModuleOrbitsChunk0.minimal j g
  by_cases h256 : i.val < 342
  · let j : Fin 86 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow6ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow6ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow6ModuleOrbitsChunk256.minimal j g
  omega

private theorem stabilizer_card (i : Fin 342) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow6ModuleRepresentation.representation (PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow6ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow6ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow6ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow6ModuleOrbitsChunk0.stabilizer_card j
  by_cases h256 : i.val < 342
  · let j : Fin 86 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow6ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow6ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow6ModuleOrbitsChunk256.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow6ModuleRepresentation.representation PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow6ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow6ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 342) :
    (PrimitiveAffineEightFrameRow6ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow6ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow6ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow6ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow6ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow6ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow6ModuleOrbitsChunk0.orbit_mem_chart j
  by_cases h256 : i.val < 342
  · let j : Fin 86 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow6ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow6ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow6ModuleOrbitsChunk256.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 342) :
    PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow6ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow6ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow6ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 342) :
    PrimitiveAffineEightFrameRow6ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow6ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow6ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow6ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow6ModuleOrbitsChunk0.canonical_mem_orbit_span j
  by_cases h256 : i.val < 342
  · let j : Fin 86 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow6ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow6ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow6ModuleOrbitsChunk256.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 342) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow6ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow6ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow6ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow6ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow6ModuleRepresentation.states (PrimitiveAffineEightFrameRow6ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow6ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow6ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow6ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow6ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow6ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow6ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleOrbits

end
