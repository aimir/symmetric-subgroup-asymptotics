import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleOrbitsChunk0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleOrbitsChunk256
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleOrbitsChunk512
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleOrbitsChunk768
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1024
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1280
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1536
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1792
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2048
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2304
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2560

/-! Selected row 0 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow0ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow0TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow0ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 2812) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow0ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk0.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk0.minimal j g
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk256.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk256.minimal j g
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk512.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk512.minimal j g
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk768.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk768.minimal j g
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1024.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1024.minimal j g
  by_cases h1280 : i.val < 1536
  · let j : Fin 256 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1280.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1280.minimal j g
  by_cases h1536 : i.val < 1792
  · let j : Fin 256 := ⟨i.val - 1536, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1536.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1536.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1536.minimal j g
  by_cases h1792 : i.val < 2048
  · let j : Fin 256 := ⟨i.val - 1792, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1792.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1792.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1792.minimal j g
  by_cases h2048 : i.val < 2304
  · let j : Fin 256 := ⟨i.val - 2048, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2048.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2048.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2048.minimal j g
  by_cases h2304 : i.val < 2560
  · let j : Fin 256 := ⟨i.val - 2304, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2304.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2304.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2304.minimal j g
  by_cases h2560 : i.val < 2812
  · let j : Fin 252 := ⟨i.val - 2560, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2560.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2560.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2560.minimal j g
  omega

private theorem stabilizer_card (i : Fin 2812) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation (PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow0ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk0.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk0.stabilizer_card j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk256.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk256.stabilizer_card j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk512.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk512.stabilizer_card j
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk768.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk768.stabilizer_card j
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1024.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1024.stabilizer_card j
  by_cases h1280 : i.val < 1536
  · let j : Fin 256 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1280.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1280.stabilizer_card j
  by_cases h1536 : i.val < 1792
  · let j : Fin 256 := ⟨i.val - 1536, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1536.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1536.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1536.stabilizer_card j
  by_cases h1792 : i.val < 2048
  · let j : Fin 256 := ⟨i.val - 1792, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1792.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1792.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1792.stabilizer_card j
  by_cases h2048 : i.val < 2304
  · let j : Fin 256 := ⟨i.val - 2048, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2048.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2048.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2048.stabilizer_card j
  by_cases h2304 : i.val < 2560
  · let j : Fin 256 := ⟨i.val - 2304, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2304.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2304.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2304.stabilizer_card j
  by_cases h2560 : i.val < 2812
  · let j : Fin 252 := ⟨i.val - 2560, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2560.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2560.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2560.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow0ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow0ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 2812) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow0ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow0ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk0.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk0.orbit_mem_chart j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk256.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk256.orbit_mem_chart j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk512.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk512.orbit_mem_chart j
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk768.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk768.orbit_mem_chart j
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1024.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1024.orbit_mem_chart j
  by_cases h1280 : i.val < 1536
  · let j : Fin 256 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1280.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1280.orbit_mem_chart j
  by_cases h1536 : i.val < 1792
  · let j : Fin 256 := ⟨i.val - 1536, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1536.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1536.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1536.orbit_mem_chart j
  by_cases h1792 : i.val < 2048
  · let j : Fin 256 := ⟨i.val - 1792, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1792.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1792.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1792.orbit_mem_chart j
  by_cases h2048 : i.val < 2304
  · let j : Fin 256 := ⟨i.val - 2048, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2048.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2048.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2048.orbit_mem_chart j
  by_cases h2304 : i.val < 2560
  · let j : Fin 256 := ⟨i.val - 2304, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2304.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2304.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2304.orbit_mem_chart j
  by_cases h2560 : i.val < 2812
  · let j : Fin 252 := ⟨i.val - 2560, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2560.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2560.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2560.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 2812) :
    PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow0ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow0ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 2812) :
    PrimitiveAffineEightFrameRow0ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow0ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk0.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk0.canonical_mem_orbit_span j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk256.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk256.canonical_mem_orbit_span j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk512.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk512.canonical_mem_orbit_span j
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk768.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk768.canonical_mem_orbit_span j
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1024.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1024.canonical_mem_orbit_span j
  by_cases h1280 : i.val < 1536
  · let j : Fin 256 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1280.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1280.canonical_mem_orbit_span j
  by_cases h1536 : i.val < 1792
  · let j : Fin 256 := ⟨i.val - 1536, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1536.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1536.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1536.canonical_mem_orbit_span j
  by_cases h1792 : i.val < 2048
  · let j : Fin 256 := ⟨i.val - 1792, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1792.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1792.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk1792.canonical_mem_orbit_span j
  by_cases h2048 : i.val < 2304
  · let j : Fin 256 := ⟨i.val - 2048, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2048.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2048.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2048.canonical_mem_orbit_span j
  by_cases h2304 : i.val < 2560
  · let j : Fin 256 := ⟨i.val - 2304, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2304.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2304.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2304.canonical_mem_orbit_span j
  by_cases h2560 : i.val < 2812
  · let j : Fin 252 := ⟨i.val - 2560, by omega⟩
    have hj : PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2560.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2560.embed, j] <;> omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow0ModuleOrbitsChunk2560.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 2812) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow0ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow0ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow0ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow0ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states (PrimitiveAffineEightFrameRow0ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow0ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow0ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow0ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow0ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow0ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow0ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleOrbits

end
