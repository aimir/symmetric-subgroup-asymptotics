import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleOrbitsChunk0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleOrbitsChunk256
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleOrbitsChunk512
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleOrbitsChunk768

/-! Selected row 22 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow22ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop13TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow22ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 865) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow22ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow22ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow22ModuleOrbitsChunk0.minimal j g
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow22ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow22ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow22ModuleOrbitsChunk256.minimal j g
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow22ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow22ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow22ModuleOrbitsChunk512.minimal j g
  by_cases h768 : i.val < 865
  · let j : Fin 97 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow22ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow22ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow22ModuleOrbitsChunk768.minimal j g
  omega

private theorem stabilizer_card (i : Fin 865) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow22ModuleRepresentation.representation (PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow22ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow22ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow22ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow22ModuleOrbitsChunk0.stabilizer_card j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow22ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow22ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow22ModuleOrbitsChunk256.stabilizer_card j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow22ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow22ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow22ModuleOrbitsChunk512.stabilizer_card j
  by_cases h768 : i.val < 865
  · let j : Fin 97 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow22ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow22ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow22ModuleOrbitsChunk768.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow22ModuleRepresentation.representation PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow22ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow22ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 865) :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow22ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow22ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow22ModuleOrbitsChunk0.orbit_mem_chart j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow22ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow22ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow22ModuleOrbitsChunk256.orbit_mem_chart j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow22ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow22ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow22ModuleOrbitsChunk512.orbit_mem_chart j
  by_cases h768 : i.val < 865
  · let j : Fin 97 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow22ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow22ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow22ModuleOrbitsChunk768.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 865) :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 865) :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow22ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow22ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow22ModuleOrbitsChunk0.canonical_mem_orbit_span j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow22ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow22ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow22ModuleOrbitsChunk256.canonical_mem_orbit_span j
  by_cases h512 : i.val < 768
  · let j : Fin 256 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow22ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow22ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow22ModuleOrbitsChunk512.canonical_mem_orbit_span j
  by_cases h768 : i.val < 865
  · let j : Fin 97 := ⟨i.val - 768, by omega⟩
    have hj : PrimitiveAffineEightFrameRow22ModuleOrbitsChunk768.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow22ModuleOrbitsChunk768.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow22ModuleOrbitsChunk768.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 865) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow22ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow22ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow22ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleOrbits

end
