import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleOrbitsChunk0

/-! Selected row 17 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow17ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow17ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 226) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow17ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 226
  · let j : Fin 226 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow17ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow17ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow17ModuleOrbitsChunk0.minimal j g
  omega

private theorem stabilizer_card (i : Fin 226) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow17ModuleRepresentation.representation (PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow17ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 226
  · let j : Fin 226 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow17ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow17ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow17ModuleOrbitsChunk0.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow17ModuleRepresentation.representation PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow17ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow17ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 226) :
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow17ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow17ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow17ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 226
  · let j : Fin 226 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow17ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow17ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow17ModuleOrbitsChunk0.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 226) :
    PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow17ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow17ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow17ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 226) :
    PrimitiveAffineEightFrameRow17ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow17ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 226
  · let j : Fin 226 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow17ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow17ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow17ModuleOrbitsChunk0.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 226) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow17ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow17ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow17ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow17ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.states (PrimitiveAffineEightFrameRow17ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow17ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow17ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow17ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow17ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow17ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow17ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleOrbits

end
