import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleOrbitsChunk0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleOrbitsChunk256

/-! Selected row 4 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow4ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow4TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow4ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 366) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow4ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow4ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow4ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow4ModuleOrbitsChunk0.minimal j g
  by_cases h256 : i.val < 366
  · let j : Fin 110 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow4ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow4ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow4ModuleOrbitsChunk256.minimal j g
  omega

private theorem stabilizer_card (i : Fin 366) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow4ModuleRepresentation.representation (PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow4ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow4ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow4ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow4ModuleOrbitsChunk0.stabilizer_card j
  by_cases h256 : i.val < 366
  · let j : Fin 110 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow4ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow4ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow4ModuleOrbitsChunk256.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow4ModuleRepresentation.representation PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow4ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow4ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 366) :
    (PrimitiveAffineEightFrameRow4ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow4ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow4ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow4ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow4ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow4ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow4ModuleOrbitsChunk0.orbit_mem_chart j
  by_cases h256 : i.val < 366
  · let j : Fin 110 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow4ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow4ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow4ModuleOrbitsChunk256.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 366) :
    PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow4ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow4ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow4ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow4ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow4ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 366) :
    PrimitiveAffineEightFrameRow4ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow4ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow4ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow4ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow4ModuleOrbitsChunk0.canonical_mem_orbit_span j
  by_cases h256 : i.val < 366
  · let j : Fin 110 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow4ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow4ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow4ModuleOrbitsChunk256.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 366) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow4ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow4ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow4ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow4ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow4ModuleRepresentation.states (PrimitiveAffineEightFrameRow4ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow4ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow4ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow4ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow4ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow4ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow4ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleOrbits

end
