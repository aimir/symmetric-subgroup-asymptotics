import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21ModuleOrbitsChunk0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21ModuleOrbitsChunk256
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21ModuleOrbitsChunk512
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21ModuleOrbitsChunk768

/-! Selected row 21 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow21ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow21TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow21ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 982) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow21ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow21ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow21ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow21ModuleOrbitsChunk0.minimal j g
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow21ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow21ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow21ModuleOrbitsChunk256.minimal j g
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow21ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow21ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow21ModuleOrbitsChunk512.minimal j g
  by_cases h768 : i.val < 982
  · let j : Fin 214 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow21ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow21ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow21ModuleOrbitsChunk768.minimal j g
  omega

private theorem stabilizer_card (i : Fin 982) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow21ModuleRepresentation.representation (PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow21ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow21ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow21ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow21ModuleOrbitsChunk0.stabilizer_card j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow21ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow21ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow21ModuleOrbitsChunk256.stabilizer_card j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow21ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow21ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow21ModuleOrbitsChunk512.stabilizer_card j
  by_cases h768 : i.val < 982
  · let j : Fin 214 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow21ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow21ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow21ModuleOrbitsChunk768.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow21ModuleRepresentation.representation PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow21ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow21ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 982) :
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow21ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow21ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow21ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow21ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow21ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow21ModuleOrbitsChunk0.orbit_mem_chart j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow21ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow21ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow21ModuleOrbitsChunk256.orbit_mem_chart j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow21ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow21ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow21ModuleOrbitsChunk512.orbit_mem_chart j
  by_cases h768 : i.val < 982
  · let j : Fin 214 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow21ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow21ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow21ModuleOrbitsChunk768.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 982) :
    PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow21ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow21ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow21ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 982) :
    PrimitiveAffineEightFrameRow21ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow21ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow21ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow21ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow21ModuleOrbitsChunk0.canonical_mem_orbit_span j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow21ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow21ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow21ModuleOrbitsChunk256.canonical_mem_orbit_span j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow21ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow21ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow21ModuleOrbitsChunk512.canonical_mem_orbit_span j
  by_cases h768 : i.val < 982
  · let j : Fin 214 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow21ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow21ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow21ModuleOrbitsChunk768.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 982) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow21ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow21ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow21ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow21ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.states (PrimitiveAffineEightFrameRow21ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow21ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow21ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow21ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow21ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow21ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow21ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21ModuleOrbits

end
