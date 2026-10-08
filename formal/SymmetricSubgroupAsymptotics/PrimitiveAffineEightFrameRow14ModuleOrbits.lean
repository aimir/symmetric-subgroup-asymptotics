import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow14ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow14ModuleOrbitsChunk0

/-! Selected row 14 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow14ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow14ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow14ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 198) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow14ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 198
  · let j : Fin 198 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow14ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow14ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow14ModuleOrbitsChunk0.minimal j g
  omega

private theorem stabilizer_card (i : Fin 198) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow14ModuleRepresentation.representation (PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow14ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 198
  · let j : Fin 198 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow14ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow14ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow14ModuleOrbitsChunk0.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow14ModuleRepresentation.representation PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow14ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow14ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 198) :
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow14ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 198
  · let j : Fin 198 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow14ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow14ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow14ModuleOrbitsChunk0.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 198) :
    PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow14ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow14ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow14ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 198) :
    PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 198
  · let j : Fin 198 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow14ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow14ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow14ModuleOrbitsChunk0.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 198) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow14ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow14ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow14ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow14ModuleOrbits

end
