import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleOrbitsChunk0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleOrbitsChunk256
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleOrbitsChunk512

/-! Selected row 25 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow25ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop16TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow25ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 532) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow25ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow25ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow25ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow25ModuleOrbitsChunk0.minimal j g
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow25ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow25ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow25ModuleOrbitsChunk256.minimal j g
  by_cases h512 : i.val < 532
  · let j : Fin 20 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow25ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow25ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow25ModuleOrbitsChunk512.minimal j g
  omega

private theorem stabilizer_card (i : Fin 532) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow25ModuleRepresentation.representation (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow25ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow25ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow25ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow25ModuleOrbitsChunk0.stabilizer_card j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow25ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow25ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow25ModuleOrbitsChunk256.stabilizer_card j
  by_cases h512 : i.val < 532
  · let j : Fin 20 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow25ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow25ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow25ModuleOrbitsChunk512.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow25ModuleRepresentation.representation PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow25ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow25ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 532) :
    (PrimitiveAffineEightFrameRow25ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow25ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow25ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow25ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow25ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow25ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow25ModuleOrbitsChunk0.orbit_mem_chart j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow25ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow25ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow25ModuleOrbitsChunk256.orbit_mem_chart j
  by_cases h512 : i.val < 532
  · let j : Fin 20 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow25ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow25ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow25ModuleOrbitsChunk512.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 532) :
    PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow25ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow25ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow25ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow25ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow25ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 532) :
    PrimitiveAffineEightFrameRow25ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow25ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow25ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow25ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow25ModuleOrbitsChunk0.canonical_mem_orbit_span j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow25ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow25ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow25ModuleOrbitsChunk256.canonical_mem_orbit_span j
  by_cases h512 : i.val < 532
  · let j : Fin 20 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow25ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow25ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow25ModuleOrbitsChunk512.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 532) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow25ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow25ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow25ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow25ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow25ModuleRepresentation.states (PrimitiveAffineEightFrameRow25ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow25ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow25ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow25ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow25ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow25ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow25ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleOrbits

end
