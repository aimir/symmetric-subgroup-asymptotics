import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleOrbitsChunk0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleOrbitsChunk256

/-! Selected row 5 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow5ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow5TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow5ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 370) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow5ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow5ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow5ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow5ModuleOrbitsChunk0.minimal j g
  by_cases h256 : i.val < 370
  · let j : Fin 114 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow5ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow5ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow5ModuleOrbitsChunk256.minimal j g
  omega

private theorem stabilizer_card (i : Fin 370) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow5ModuleRepresentation.representation (PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow5ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow5ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow5ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow5ModuleOrbitsChunk0.stabilizer_card j
  by_cases h256 : i.val < 370
  · let j : Fin 114 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow5ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow5ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow5ModuleOrbitsChunk256.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow5ModuleRepresentation.representation PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow5ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow5ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 370) :
    (PrimitiveAffineEightFrameRow5ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow5ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow5ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow5ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow5ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow5ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow5ModuleOrbitsChunk0.orbit_mem_chart j
  by_cases h256 : i.val < 370
  · let j : Fin 114 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow5ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow5ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow5ModuleOrbitsChunk256.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 370) :
    PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow5ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow5ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow5ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow5ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow5ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 370) :
    PrimitiveAffineEightFrameRow5ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow5ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow5ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow5ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow5ModuleOrbitsChunk0.canonical_mem_orbit_span j
  by_cases h256 : i.val < 370
  · let j : Fin 114 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow5ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow5ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow5ModuleOrbitsChunk256.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 370) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow5ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow5ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow5ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow5ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow5ModuleRepresentation.states (PrimitiveAffineEightFrameRow5ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow5ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow5ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow5ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow5ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow5ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow5ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleOrbits

end
