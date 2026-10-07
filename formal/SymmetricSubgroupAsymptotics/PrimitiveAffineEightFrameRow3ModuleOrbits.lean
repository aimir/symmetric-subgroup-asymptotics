import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleOrbitsChunk0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleOrbitsChunk256
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleOrbitsChunk512
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleOrbitsChunk768

/-! Selected row 3 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow3ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow3TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow3ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 1006) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow3ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow3ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow3ModuleOrbitsChunk0.minimal j g
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow3ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow3ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow3ModuleOrbitsChunk256.minimal j g
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow3ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow3ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow3ModuleOrbitsChunk512.minimal j g
  by_cases h768 : i.val < 1006
  · let j : Fin 238 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow3ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow3ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow3ModuleOrbitsChunk768.minimal j g
  omega

private theorem stabilizer_card (i : Fin 1006) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation (PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow3ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow3ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow3ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow3ModuleOrbitsChunk0.stabilizer_card j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow3ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow3ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow3ModuleOrbitsChunk256.stabilizer_card j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow3ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow3ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow3ModuleOrbitsChunk512.stabilizer_card j
  by_cases h768 : i.val < 1006
  · let j : Fin 238 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow3ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow3ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow3ModuleOrbitsChunk768.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow3ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow3ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 1006) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow3ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow3ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow3ModuleOrbitsChunk0.orbit_mem_chart j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow3ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow3ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow3ModuleOrbitsChunk256.orbit_mem_chart j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow3ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow3ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow3ModuleOrbitsChunk512.orbit_mem_chart j
  by_cases h768 : i.val < 1006
  · let j : Fin 238 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow3ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow3ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow3ModuleOrbitsChunk768.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 1006) :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 1006) :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow3ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow3ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow3ModuleOrbitsChunk0.canonical_mem_orbit_span j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow3ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow3ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow3ModuleOrbitsChunk256.canonical_mem_orbit_span j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow3ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow3ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow3ModuleOrbitsChunk512.canonical_mem_orbit_span j
  by_cases h768 : i.val < 1006
  · let j : Fin 238 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow3ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow3ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow3ModuleOrbitsChunk768.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 1006) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow3ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow3ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow3ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleOrbits

end
