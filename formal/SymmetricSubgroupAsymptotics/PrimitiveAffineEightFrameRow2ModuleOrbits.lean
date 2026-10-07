import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleOrbitsChunk0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleOrbitsChunk256
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleOrbitsChunk512
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleOrbitsChunk768

/-! Selected row 2 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow2ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow2TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow2ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 982) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow2ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow2ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow2ModuleOrbitsChunk0.minimal j g
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow2ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow2ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow2ModuleOrbitsChunk256.minimal j g
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow2ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow2ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow2ModuleOrbitsChunk512.minimal j g
  by_cases h768 : i.val < 982
  · let j : Fin 214 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow2ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow2ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow2ModuleOrbitsChunk768.minimal j g
  omega

private theorem stabilizer_card (i : Fin 982) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow2ModuleRepresentation.representation (PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow2ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow2ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow2ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow2ModuleOrbitsChunk0.stabilizer_card j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow2ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow2ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow2ModuleOrbitsChunk256.stabilizer_card j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow2ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow2ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow2ModuleOrbitsChunk512.stabilizer_card j
  by_cases h768 : i.val < 982
  · let j : Fin 214 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow2ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow2ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow2ModuleOrbitsChunk768.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow2ModuleRepresentation.representation PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow2ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow2ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 982) :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow2ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow2ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow2ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow2ModuleOrbitsChunk0.orbit_mem_chart j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow2ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow2ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow2ModuleOrbitsChunk256.orbit_mem_chart j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow2ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow2ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow2ModuleOrbitsChunk512.orbit_mem_chart j
  by_cases h768 : i.val < 982
  · let j : Fin 214 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow2ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow2ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow2ModuleOrbitsChunk768.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 982) :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow2ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 982) :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow2ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow2ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow2ModuleOrbitsChunk0.canonical_mem_orbit_span j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow2ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow2ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow2ModuleOrbitsChunk256.canonical_mem_orbit_span j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow2ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow2ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow2ModuleOrbitsChunk512.canonical_mem_orbit_span j
  by_cases h768 : i.val < 982
  · let j : Fin 214 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow2ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow2ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow2ModuleOrbitsChunk768.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 982) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow2ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow2ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow2ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleOrbits

end
