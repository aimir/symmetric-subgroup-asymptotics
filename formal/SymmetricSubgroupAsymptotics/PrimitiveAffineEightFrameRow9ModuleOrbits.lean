import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleOrbitsChunk0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleOrbitsChunk256
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleOrbitsChunk512

/-! Selected row 9 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow9ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow9TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow9ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 535) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow9ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow9ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow9ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow9ModuleOrbitsChunk0.minimal j g
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow9ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow9ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow9ModuleOrbitsChunk256.minimal j g
  by_cases h512 : i.val < 535
  · let j : Fin 23 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow9ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow9ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow9ModuleOrbitsChunk512.minimal j g
  omega

private theorem stabilizer_card (i : Fin 535) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow9ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow9ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow9ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow9ModuleOrbitsChunk0.stabilizer_card j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow9ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow9ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow9ModuleOrbitsChunk256.stabilizer_card j
  by_cases h512 : i.val < 535
  · let j : Fin 23 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow9ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow9ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow9ModuleOrbitsChunk512.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow9ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow9ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 535) :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow9ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow9ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow9ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow9ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow9ModuleOrbitsChunk0.orbit_mem_chart j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow9ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow9ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow9ModuleOrbitsChunk256.orbit_mem_chart j
  by_cases h512 : i.val < 535
  · let j : Fin 23 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow9ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow9ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow9ModuleOrbitsChunk512.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 535) :
    PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow9ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow9ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 535) :
    PrimitiveAffineEightFrameRow9ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow9ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow9ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow9ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow9ModuleOrbitsChunk0.canonical_mem_orbit_span j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow9ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow9ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow9ModuleOrbitsChunk256.canonical_mem_orbit_span j
  by_cases h512 : i.val < 535
  · let j : Fin 23 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow9ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow9ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow9ModuleOrbitsChunk512.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 535) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow9ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow9ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow9ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow9ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states (PrimitiveAffineEightFrameRow9ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow9ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow9ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow9ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow9ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow9ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow9ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleOrbits

end
