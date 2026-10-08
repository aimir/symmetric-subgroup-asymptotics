import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleOrbitsChunk0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleOrbitsChunk256

/-! Selected row 26 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow26ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop17TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow26ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 475) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow26ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow26ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow26ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow26ModuleOrbitsChunk0.minimal j g
  by_cases h256 : i.val < 475
  · let j : Fin 219 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow26ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow26ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow26ModuleOrbitsChunk256.minimal j g
  omega

private theorem stabilizer_card (i : Fin 475) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow26ModuleRepresentation.representation (PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow26ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow26ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow26ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow26ModuleOrbitsChunk0.stabilizer_card j
  by_cases h256 : i.val < 475
  · let j : Fin 219 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow26ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow26ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow26ModuleOrbitsChunk256.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow26ModuleRepresentation.representation PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow26ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow26ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 475) :
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow26ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow26ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow26ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow26ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow26ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow26ModuleOrbitsChunk0.orbit_mem_chart j
  by_cases h256 : i.val < 475
  · let j : Fin 219 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow26ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow26ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow26ModuleOrbitsChunk256.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 475) :
    PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow26ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow26ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow26ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 475) :
    PrimitiveAffineEightFrameRow26ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow26ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow26ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow26ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow26ModuleOrbitsChunk0.canonical_mem_orbit_span j
  by_cases h256 : i.val < 475
  · let j : Fin 219 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow26ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow26ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow26ModuleOrbitsChunk256.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 475) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow26ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow26ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow26ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow26ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states (PrimitiveAffineEightFrameRow26ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow26ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow26ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow26ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow26ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow26ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow26ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleOrbits

end
