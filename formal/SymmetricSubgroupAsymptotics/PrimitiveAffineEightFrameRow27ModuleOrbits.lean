import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ModuleOrbitsChunk0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ModuleOrbitsChunk256

/-! Selected row 27 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow27ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow27TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow27ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 412) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow27ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow27ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow27ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow27ModuleOrbitsChunk0.minimal j g
  by_cases h256 : i.val < 412
  · let j : Fin 156 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow27ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow27ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow27ModuleOrbitsChunk256.minimal j g
  omega

private theorem stabilizer_card (i : Fin 412) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow27ModuleRepresentation.representation (PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow27ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow27ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow27ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow27ModuleOrbitsChunk0.stabilizer_card j
  by_cases h256 : i.val < 412
  · let j : Fin 156 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow27ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow27ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow27ModuleOrbitsChunk256.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow27ModuleRepresentation.representation PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow27ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow27ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 412) :
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow27ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow27ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow27ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow27ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow27ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow27ModuleOrbitsChunk0.orbit_mem_chart j
  by_cases h256 : i.val < 412
  · let j : Fin 156 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow27ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow27ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow27ModuleOrbitsChunk256.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 412) :
    PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow27ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow27ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow27ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 412) :
    PrimitiveAffineEightFrameRow27ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow27ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow27ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow27ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow27ModuleOrbitsChunk0.canonical_mem_orbit_span j
  by_cases h256 : i.val < 412
  · let j : Fin 156 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow27ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow27ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow27ModuleOrbitsChunk256.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 412) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow27ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow27ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow27ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow27ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.states (PrimitiveAffineEightFrameRow27ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow27ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow27ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow27ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow27ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow27ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow27ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ModuleOrbits

end
