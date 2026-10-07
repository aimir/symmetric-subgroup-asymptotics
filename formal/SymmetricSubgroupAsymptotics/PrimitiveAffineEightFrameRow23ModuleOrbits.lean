import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleOrbitsChunk0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleOrbitsChunk256
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleOrbitsChunk512
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleOrbitsChunk768
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1024
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1280

/-! Selected row 23 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow23ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow23TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow23ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 1441) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow23ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk0.minimal j g
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk256.minimal j g
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk512.minimal j g
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk768.minimal j g
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1024.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1024.minimal j g
  by_cases h1280 : i.val < 1441
  · let j : Fin 161 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1280.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1280.minimal j g
  omega

private theorem stabilizer_card (i : Fin 1441) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation (PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow23ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk0.stabilizer_card j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk256.stabilizer_card j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk512.stabilizer_card j
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk768.stabilizer_card j
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1024.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1024.stabilizer_card j
  by_cases h1280 : i.val < 1441
  · let j : Fin 161 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1280.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1280.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow23ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow23ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 1441) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow23ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow23ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk0.orbit_mem_chart j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk256.orbit_mem_chart j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk512.orbit_mem_chart j
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk768.orbit_mem_chart j
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1024.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1024.orbit_mem_chart j
  by_cases h1280 : i.val < 1441
  · let j : Fin 161 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1280.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1280.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 1441) :
    PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow23ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow23ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 1441) :
    PrimitiveAffineEightFrameRow23ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow23ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk0.canonical_mem_orbit_span j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk256.canonical_mem_orbit_span j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk512.canonical_mem_orbit_span j
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk768.canonical_mem_orbit_span j
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1024.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1024.canonical_mem_orbit_span j
  by_cases h1280 : i.val < 1441
  · let j : Fin 161 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1280.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow23ModuleOrbitsChunk1280.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 1441) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow23ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow23ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow23ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow23ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states (PrimitiveAffineEightFrameRow23ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow23ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow23ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow23ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow23ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow23ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow23ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleOrbits

end
