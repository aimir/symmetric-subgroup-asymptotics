import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleOrbitsChunk0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleOrbitsChunk256

/-! Selected row 7 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow7ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow7TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow7ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 406) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow7ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow7ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow7ModuleOrbitsChunk0.minimal j g
  by_cases h256 : i.val < 406
  · let j : Fin 150 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow7ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow7ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow7ModuleOrbitsChunk256.minimal j g
  omega

private theorem stabilizer_card (i : Fin 406) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow7ModuleRepresentation.representation (PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow7ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow7ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow7ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow7ModuleOrbitsChunk0.stabilizer_card j
  by_cases h256 : i.val < 406
  · let j : Fin 150 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow7ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow7ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow7ModuleOrbitsChunk256.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow7ModuleRepresentation.representation PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow7ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow7ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 406) :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow7ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow7ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow7ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow7ModuleOrbitsChunk0.orbit_mem_chart j
  by_cases h256 : i.val < 406
  · let j : Fin 150 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow7ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow7ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow7ModuleOrbitsChunk256.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 406) :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow7ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 406) :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow7ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow7ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow7ModuleOrbitsChunk0.canonical_mem_orbit_span j
  by_cases h256 : i.val < 406
  · let j : Fin 150 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow7ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow7ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow7ModuleOrbitsChunk256.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 406) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow7ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow7ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow7ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleOrbits

end
