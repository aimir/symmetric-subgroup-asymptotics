import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleOrbitsCanonical
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleOrbitsChunk0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleOrbitsChunk256
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleOrbitsChunk512

/-! Selected row 24 complete bounded orbit cover. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleOrbits

abbrev Source := PrimitiveAffineEightFrameRow24ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop15TopCertificate.group
abbrev ModelModule := PrimitiveAffineEightFrameRow24ModuleRepresentation.ModelModule

private theorem representative_minimal (i : Fin 535) (g : Source) :
    binaryVectorMask (PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitRepresentative i) ≤
      binaryVectorMask (PrimitiveAffineEightFrameRow24ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitRepresentative i)) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow24ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow24ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow24ModuleOrbitsChunk0.minimal j g
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow24ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow24ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow24ModuleOrbitsChunk256.minimal j g
  by_cases h512 : i.val < 535
  · let j : Fin 23 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow24ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow24ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow24ModuleOrbitsChunk512.minimal j g
  omega

private theorem stabilizer_card (i : Fin 535) :
    Nat.card (representationVectorStabilizer
      PrimitiveAffineEightFrameRow24ModuleRepresentation.representation (PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitRepresentative i)) =
        PrimitiveAffineEightFrameRow24ModuleOrbitsData.stabilizerCard i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow24ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow24ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow24ModuleOrbitsChunk0.stabilizer_card j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow24ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow24ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow24ModuleOrbitsChunk256.stabilizer_card j
  by_cases h512 : i.val < 535
  · let j : Fin 23 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow24ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow24ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow24ModuleOrbitsChunk512.stabilizer_card j
  omega

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      PrimitiveAffineEightFrameRow24ModuleRepresentation.representation PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := PrimitiveAffineEightFrameRow24ModuleOrbitsData.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := PrimitiveAffineEightFrameRow24ModuleOrbitsData.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbit_card_sum

private theorem orbit_mem_chart (i : Fin 535) :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts
      (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitCyclic i))).2.inclusion
        ((PrimitiveAffineEightFrameRow24ModuleRepresentation.charts
          (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitCyclic i))).2.coordinates
          (PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitRepresentative i)) = PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitRepresentative i := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow24ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow24ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow24ModuleOrbitsChunk0.orbit_mem_chart j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow24ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow24ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow24ModuleOrbitsChunk256.orbit_mem_chart j
  by_cases h512 : i.val < 535
  · let j : Fin 23 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow24ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow24ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow24ModuleOrbitsChunk512.orbit_mem_chart j
  omega

private theorem orbit_mem_state (i : Fin 535) :
    PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitRepresentative i ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitCyclic i))).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  exact ((PrimitiveAffineEightFrameRow24ModuleRepresentation.charts
    (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitCyclic i))).2.mem_iff
      (PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin 535) :
    PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitCyclic i) ∈
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitRepresentative i) := by
  by_cases h0 : i.val < 256
  · let j : Fin 256 := ⟨i.val - 0, by omega⟩
    have hj : PrimitiveAffineEightFrameRow24ModuleOrbitsChunk0.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow24ModuleOrbitsChunk0.embed, j]
    rw [← hj]
    exact PrimitiveAffineEightFrameRow24ModuleOrbitsChunk0.canonical_mem_orbit_span j
  by_cases h256 : i.val < 512
  · let j : Fin 256 := ⟨i.val - 256, by omega⟩
    have hj : PrimitiveAffineEightFrameRow24ModuleOrbitsChunk256.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow24ModuleOrbitsChunk256.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow24ModuleOrbitsChunk256.canonical_mem_orbit_span j
  by_cases h512 : i.val < 535
  · let j : Fin 23 := ⟨i.val - 512, by omega⟩
    have hj : PrimitiveAffineEightFrameRow24ModuleOrbitsChunk512.embed j = i := by
      apply Fin.ext
      simp [PrimitiveAffineEightFrameRow24ModuleOrbitsChunk512.embed, j]
      omega
    rw [← hj]
    exact PrimitiveAffineEightFrameRow24ModuleOrbitsChunk512.canonical_mem_orbit_span j
  omega

theorem orbit_span_eq (i : Fin 535) :
    binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitRepresentative i) =
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative (PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicState (PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitCyclic i)))
    (PrimitiveAffineEightFrameRow24ModuleOrbitsCanonical.canonical_span (PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord
abbrev orbitRepresentative := PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitRepresentative
abbrev stabilizerCard := PrimitiveAffineEightFrameRow24ModuleOrbitsData.stabilizerCard
abbrev orbitCyclic := PrimitiveAffineEightFrameRow24ModuleOrbitsData.orbitCyclic
abbrev cyclicRepresentative := PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative
abbrev cyclicState := PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicState

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleOrbits

end
