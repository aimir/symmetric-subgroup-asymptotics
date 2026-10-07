import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleOrbitsChunk0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleOrbitsChunk256
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleOrbitsChunk512
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleOrbitsChunk768
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1024
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1280

/-! Selected row 8 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow8ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow8TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow8ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 1474) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow8ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk0.minimal j g
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk256.minimal j g
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk512.minimal j g
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk768.minimal j g
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1024.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1024.minimal j g
  by_cases h1280 : i.val < 1474
  · let j : Fin 194 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1280.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1280.minimal j g
  omega

private theorem stabilizer_card (i : Fin 1474) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow8ModuleRepresentation.representation (PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow8ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk0.stabilizer_card j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk256.stabilizer_card j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk512.stabilizer_card j
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk768.stabilizer_card j
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1024.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1024.stabilizer_card j
  by_cases h1280 : i.val < 1474
  · let j : Fin 194 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1280.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1280.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow8ModuleRepresentation.representation PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow8ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow8ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 1474) :
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow8ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow8ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow8ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk0.orbit_mem_chart j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk256.orbit_mem_chart j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk512.orbit_mem_chart j
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk768.orbit_mem_chart j
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1024.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1024.orbit_mem_chart j
  by_cases h1280 : i.val < 1474
  · let j : Fin 194 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1280.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1280.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 1474) :
    PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow8ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow8ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow8ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 1474) :
    PrimitiveAffineEightFrameRow8ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow8ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk0.canonical_mem_orbit_span j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk256.canonical_mem_orbit_span j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk512.canonical_mem_orbit_span j
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk768.canonical_mem_orbit_span j
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1024.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1024.canonical_mem_orbit_span j
  by_cases h1280 : i.val < 1474
  · let j : Fin 194 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1280.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow8ModuleOrbitsChunk1280.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 1474) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow8ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow8ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow8ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow8ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.states (PrimitiveAffineEightFrameRow8ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow8ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow8ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow8ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow8ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow8ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow8ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleOrbits

end
