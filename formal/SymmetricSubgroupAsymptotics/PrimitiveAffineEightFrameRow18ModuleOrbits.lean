import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleOrbitsChunk0

/-! Selected row 18 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow18ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop10TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow18ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 150) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow18ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 150
  · let j : Fin 150 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow18ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow18ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow18ModuleOrbitsChunk0.minimal j g
  omega

private theorem stabilizer_card (i : Fin 150) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow18ModuleRepresentation.representation (PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow18ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 150
  · let j : Fin 150 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow18ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow18ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow18ModuleOrbitsChunk0.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow18ModuleRepresentation.representation PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow18ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow18ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 150) :
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow18ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 150
  · let j : Fin 150 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow18ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow18ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow18ModuleOrbitsChunk0.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 150) :
    PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow18ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow18ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow18ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 150) :
    PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow18ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 150
  · let j : Fin 150 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow18ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow18ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow18ModuleOrbitsChunk0.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 150) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow18ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow18ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow18ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.states (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow18ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow18ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow18ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleOrbits

end
