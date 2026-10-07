import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ModuleRegistryJoin0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ModuleRegistryJoin8

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameRow27TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 11) (c : Fin 11) :
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow27ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow27ModuleOrbits.cyclicRepresentative c) := by
  by_cases h0 : i.val < 8
  · let j : Fin 8 := ⟨i.val - 0, by omega⟩
    have hj : JoinChunk0.embed j = i := by
      apply Fin.ext
      simp [JoinChunk0.embed, j]
    rw [← hj]
    exact JoinChunk0.child_eq j c
  by_cases h8 : i.val < 11
  · let j : Fin 3 := ⟨i.val - 8, by omega⟩
    have hj : JoinChunk8.embed j = i := by
      apply Fin.ext
      simp [JoinChunk8.embed, j]
      omega
    rw [← hj]
    exact JoinChunk8.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.states (0 : Fin 11)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow27ModuleRepresentation.charts (0 : Fin 11)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow27ModuleRepresentation.representation PrimitiveAffineEightFrameRow27ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow27ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow27ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow27ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow27ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow27ModuleOrbits.orbit_span_eq (0 : Fin 11) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ModuleRegistry

end
