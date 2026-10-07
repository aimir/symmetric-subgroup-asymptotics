import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleOrbitsChunk0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleOrbitsChunk256
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleOrbitsChunk512
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleOrbitsChunk768
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1024
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1280
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1536
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1792
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2048
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2304
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2560
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2816

/-! Selected row 1 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow1ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow1TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow1ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 2836) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk0.minimal j g
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk256.minimal j g
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk512.minimal j g
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk768.minimal j g
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1024.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1024.minimal j g
  by_cases h1280 : i.val < 1536
  · let j : Fin 256 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1280.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1280.minimal j g
  by_cases h1536 : i.val < 1792
  · let j : Fin 256 := ⟨i.val - 1536, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1536.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1536.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1536.minimal j g
  by_cases h1792 : i.val < 2048
  · let j : Fin 256 := ⟨i.val - 1792, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1792.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1792.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1792.minimal j g
  by_cases h2048 : i.val < 2304
  · let j : Fin 256 := ⟨i.val - 2048, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2048.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2048.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2048.minimal j g
  by_cases h2304 : i.val < 2560
  · let j : Fin 256 := ⟨i.val - 2304, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2304.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2304.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2304.minimal j g
  by_cases h2560 : i.val < 2816
  · let j : Fin 256 := ⟨i.val - 2560, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2560.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2560.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2560.minimal j g
  by_cases h2816 : i.val < 2836
  · let j : Fin 20 := ⟨i.val - 2816, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2816.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2816.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2816.minimal j g
  omega

private theorem stabilizer_card (i : Fin 2836) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation (PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow1ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk0.stabilizer_card j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk256.stabilizer_card j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk512.stabilizer_card j
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk768.stabilizer_card j
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1024.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1024.stabilizer_card j
  by_cases h1280 : i.val < 1536
  · let j : Fin 256 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1280.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1280.stabilizer_card j
  by_cases h1536 : i.val < 1792
  · let j : Fin 256 := ⟨i.val - 1536, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1536.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1536.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1536.stabilizer_card j
  by_cases h1792 : i.val < 2048
  · let j : Fin 256 := ⟨i.val - 1792, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1792.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1792.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1792.stabilizer_card j
  by_cases h2048 : i.val < 2304
  · let j : Fin 256 := ⟨i.val - 2048, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2048.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2048.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2048.stabilizer_card j
  by_cases h2304 : i.val < 2560
  · let j : Fin 256 := ⟨i.val - 2304, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2304.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2304.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2304.stabilizer_card j
  by_cases h2560 : i.val < 2816
  · let j : Fin 256 := ⟨i.val - 2560, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2560.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2560.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2560.stabilizer_card j
  by_cases h2816 : i.val < 2836
  · let j : Fin 20 := ⟨i.val - 2816, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2816.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2816.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2816.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow1ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow1ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 2836) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk0.orbit_mem_chart j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk256.orbit_mem_chart j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk512.orbit_mem_chart j
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk768.orbit_mem_chart j
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1024.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1024.orbit_mem_chart j
  by_cases h1280 : i.val < 1536
  · let j : Fin 256 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1280.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1280.orbit_mem_chart j
  by_cases h1536 : i.val < 1792
  · let j : Fin 256 := ⟨i.val - 1536, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1536.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1536.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1536.orbit_mem_chart j
  by_cases h1792 : i.val < 2048
  · let j : Fin 256 := ⟨i.val - 1792, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1792.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1792.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1792.orbit_mem_chart j
  by_cases h2048 : i.val < 2304
  · let j : Fin 256 := ⟨i.val - 2048, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2048.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2048.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2048.orbit_mem_chart j
  by_cases h2304 : i.val < 2560
  · let j : Fin 256 := ⟨i.val - 2304, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2304.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2304.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2304.orbit_mem_chart j
  by_cases h2560 : i.val < 2816
  · let j : Fin 256 := ⟨i.val - 2560, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2560.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2560.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2560.orbit_mem_chart j
  by_cases h2816 : i.val < 2836
  · let j : Fin 20 := ⟨i.val - 2816, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2816.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2816.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2816.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 2836) :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 2836) :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk0.canonical_mem_orbit_span j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk256.canonical_mem_orbit_span j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk512.canonical_mem_orbit_span j
  by_cases h768 : i.val < 1024
  · let j : Fin 256 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk768.canonical_mem_orbit_span j
  by_cases h1024 : i.val < 1280
  · let j : Fin 256 := ⟨i.val - 1024, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1024.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1024.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1024.canonical_mem_orbit_span j
  by_cases h1280 : i.val < 1536
  · let j : Fin 256 := ⟨i.val - 1280, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1280.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1280.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1280.canonical_mem_orbit_span j
  by_cases h1536 : i.val < 1792
  · let j : Fin 256 := ⟨i.val - 1536, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1536.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1536.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1536.canonical_mem_orbit_span j
  by_cases h1792 : i.val < 2048
  · let j : Fin 256 := ⟨i.val - 1792, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1792.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1792.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk1792.canonical_mem_orbit_span j
  by_cases h2048 : i.val < 2304
  · let j : Fin 256 := ⟨i.val - 2048, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2048.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2048.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2048.canonical_mem_orbit_span j
  by_cases h2304 : i.val < 2560
  · let j : Fin 256 := ⟨i.val - 2304, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2304.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2304.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2304.canonical_mem_orbit_span j
  by_cases h2560 : i.val < 2816
  · let j : Fin 256 := ⟨i.val - 2560, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2560.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2560.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2560.canonical_mem_orbit_span j
  by_cases h2816 : i.val < 2836
  · let j : Fin 20 := ⟨i.val - 2816, by omega⟩
    have hj : PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2816.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2816.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow1ModuleOrbitsChunk2816.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 2836) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow1ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow1ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow1ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleOrbits

end
