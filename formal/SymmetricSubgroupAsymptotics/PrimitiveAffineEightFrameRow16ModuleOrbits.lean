import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleOrbitsChunk0

/-! Selected row 16 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow16ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow16ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 194) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow16ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 194
  · let j : Fin 194 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow16ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow16ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow16ModuleOrbitsChunk0.minimal j g
  omega

private theorem stabilizer_card (i : Fin 194) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow16ModuleRepresentation.representation (PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow16ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 194
  · let j : Fin 194 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow16ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow16ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow16ModuleOrbitsChunk0.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow16ModuleRepresentation.representation PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow16ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow16ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 194) :
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow16ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 194
  · let j : Fin 194 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow16ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow16ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow16ModuleOrbitsChunk0.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 194) :
    PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow16ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 194) :
    PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 194
  · let j : Fin 194 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow16ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow16ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow16ModuleOrbitsChunk0.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 194) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow16ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow16ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow16ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleOrbits

end
