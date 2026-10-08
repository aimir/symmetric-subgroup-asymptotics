import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleOrbitsChunk0

/-! Selected row 15 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow15ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow15ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 198) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow15ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 198
  · let j : Fin 198 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow15ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow15ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow15ModuleOrbitsChunk0.minimal j g
  omega

private theorem stabilizer_card (i : Fin 198) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow15ModuleRepresentation.representation (PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow15ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 198
  · let j : Fin 198 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow15ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow15ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow15ModuleOrbitsChunk0.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow15ModuleRepresentation.representation PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow15ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow15ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 198) :
    (PrimitiveAffineEightFrameRow15ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow15ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow15ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow15ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 198
  · let j : Fin 198 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow15ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow15ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow15ModuleOrbitsChunk0.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 198) :
    PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow15ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow15ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow15ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow15ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow15ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 198) :
    PrimitiveAffineEightFrameRow15ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow15ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 198
  · let j : Fin 198 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow15ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow15ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow15ModuleOrbitsChunk0.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 198) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow15ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow15ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow15ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow15ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow15ModuleRepresentation.states (PrimitiveAffineEightFrameRow15ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow15ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow15ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow15ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow15ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow15ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow15ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleOrbits

end
