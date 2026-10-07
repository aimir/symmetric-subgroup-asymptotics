import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleOrbitsChunk0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleOrbitsChunk256
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleOrbitsChunk512
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleOrbitsChunk768
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1024
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1280
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1536
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1792
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2048
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2304
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2560

/-! Selected row 20 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow20ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow20TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow20ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 2752) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow20ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk0.minimal j g
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk256.minimal j g
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk512.minimal j g
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk768.minimal j g
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1024.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1024.minimal j g
  by_cases h1280 : i.val < 1536
  · let j : Fin 256 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1280.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1280.minimal j g
  by_cases h1536 : i.val < 1792
  · let j : Fin 256 := ⟨i.val - 1536, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1536.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1536.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1536.minimal j g
  by_cases h1792 : i.val < 2048
  · let j : Fin 256 := ⟨i.val - 1792, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1792.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1792.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1792.minimal j g
  by_cases h2048 : i.val < 2304
  · let j : Fin 256 := ⟨i.val - 2048, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2048.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2048.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2048.minimal j g
  by_cases h2304 : i.val < 2560
  · let j : Fin 256 := ⟨i.val - 2304, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2304.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2304.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2304.minimal j g
  by_cases h2560 : i.val < 2752
  · let j : Fin 192 := ⟨i.val - 2560, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2560.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2560.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2560.minimal j g
  omega

private theorem stabilizer_card (i : Fin 2752) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation (PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow20ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk0.stabilizer_card j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk256.stabilizer_card j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk512.stabilizer_card j
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk768.stabilizer_card j
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1024.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1024.stabilizer_card j
  by_cases h1280 : i.val < 1536
  · let j : Fin 256 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1280.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1280.stabilizer_card j
  by_cases h1536 : i.val < 1792
  · let j : Fin 256 := ⟨i.val - 1536, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1536.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1536.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1536.stabilizer_card j
  by_cases h1792 : i.val < 2048
  · let j : Fin 256 := ⟨i.val - 1792, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1792.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1792.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1792.stabilizer_card j
  by_cases h2048 : i.val < 2304
  · let j : Fin 256 := ⟨i.val - 2048, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2048.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2048.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2048.stabilizer_card j
  by_cases h2304 : i.val < 2560
  · let j : Fin 256 := ⟨i.val - 2304, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2304.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2304.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2304.stabilizer_card j
  by_cases h2560 : i.val < 2752
  · let j : Fin 192 := ⟨i.val - 2560, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2560.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2560.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2560.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow20ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow20ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 2752) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow20ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow20ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk0.orbit_mem_chart j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk256.orbit_mem_chart j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk512.orbit_mem_chart j
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk768.orbit_mem_chart j
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1024.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1024.orbit_mem_chart j
  by_cases h1280 : i.val < 1536
  · let j : Fin 256 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1280.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1280.orbit_mem_chart j
  by_cases h1536 : i.val < 1792
  · let j : Fin 256 := ⟨i.val - 1536, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1536.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1536.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1536.orbit_mem_chart j
  by_cases h1792 : i.val < 2048
  · let j : Fin 256 := ⟨i.val - 1792, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1792.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1792.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1792.orbit_mem_chart j
  by_cases h2048 : i.val < 2304
  · let j : Fin 256 := ⟨i.val - 2048, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2048.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2048.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2048.orbit_mem_chart j
  by_cases h2304 : i.val < 2560
  · let j : Fin 256 := ⟨i.val - 2304, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2304.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2304.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2304.orbit_mem_chart j
  by_cases h2560 : i.val < 2752
  · let j : Fin 192 := ⟨i.val - 2560, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2560.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2560.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2560.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 2752) :
    PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow20ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow20ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 2752) :
    PrimitiveAffineEightFrameRow20ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow20ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk0.canonical_mem_orbit_span j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk256.canonical_mem_orbit_span j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk512.canonical_mem_orbit_span j
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk768.canonical_mem_orbit_span j
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1024.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1024.canonical_mem_orbit_span j
  by_cases h1280 : i.val < 1536
  · let j : Fin 256 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1280.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1280.canonical_mem_orbit_span j
  by_cases h1536 : i.val < 1792
  · let j : Fin 256 := ⟨i.val - 1536, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1536.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1536.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1536.canonical_mem_orbit_span j
  by_cases h1792 : i.val < 2048
  · let j : Fin 256 := ⟨i.val - 1792, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1792.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1792.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk1792.canonical_mem_orbit_span j
  by_cases h2048 : i.val < 2304
  · let j : Fin 256 := ⟨i.val - 2048, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2048.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2048.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2048.canonical_mem_orbit_span j
  by_cases h2304 : i.val < 2560
  · let j : Fin 256 := ⟨i.val - 2304, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2304.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2304.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2304.canonical_mem_orbit_span j
  by_cases h2560 : i.val < 2752
  · let j : Fin 192 := ⟨i.val - 2560, by omega⟩
    have hj : PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2560.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2560.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow20ModuleOrbitsChunk2560.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 2752) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow20ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow20ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow20ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow20ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states (PrimitiveAffineEightFrameRow20ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow20ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow20ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow20ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow20ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow20ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow20ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleOrbits

end
