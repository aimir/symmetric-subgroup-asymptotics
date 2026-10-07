import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleOrbitsChunk0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleOrbitsChunk256

/-! Selected row 29 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow29ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow29TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow29ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 305) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow29ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow29ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow29ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow29ModuleOrbitsChunk0.minimal j g
  by_cases h256 : i.val < 305
  · let j : Fin 49 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow29ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow29ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow29ModuleOrbitsChunk256.minimal j g
  omega

private theorem stabilizer_card (i : Fin 305) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow29ModuleRepresentation.representation (PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow29ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow29ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow29ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow29ModuleOrbitsChunk0.stabilizer_card j
  by_cases h256 : i.val < 305
  · let j : Fin 49 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow29ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow29ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow29ModuleOrbitsChunk256.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow29ModuleRepresentation.representation PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow29ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow29ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 305) :
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow29ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow29ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow29ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow29ModuleOrbitsChunk0.orbit_mem_chart j
  by_cases h256 : i.val < 305
  · let j : Fin 49 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow29ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow29ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow29ModuleOrbitsChunk256.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 305) :
    PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow29ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 305) :
    PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow29ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow29ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow29ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow29ModuleOrbitsChunk0.canonical_mem_orbit_span j
  by_cases h256 : i.val < 305
  · let j : Fin 49 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow29ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow29ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow29ModuleOrbitsChunk256.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 305) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow29ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow29ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow29ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow29ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow29ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow29ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleOrbits

end
