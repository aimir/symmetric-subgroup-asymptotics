import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleOrbitsChunk0

/-! Selected row 19 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow19ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop10TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow19ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 190) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow19ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 190
  · let j : Fin 190 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow19ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow19ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow19ModuleOrbitsChunk0.minimal j g
  omega

private theorem stabilizer_card (i : Fin 190) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow19ModuleRepresentation.representation (PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow19ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 190
  · let j : Fin 190 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow19ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow19ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow19ModuleOrbitsChunk0.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow19ModuleRepresentation.representation PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow19ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow19ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 190) :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow19ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 190
  · let j : Fin 190 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow19ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow19ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow19ModuleOrbitsChunk0.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 190) :
    PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow19ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 190) :
    PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 190
  · let j : Fin 190 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow19ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow19ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow19ModuleOrbitsChunk0.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 190) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow19ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow19ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow19ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleOrbits

end
