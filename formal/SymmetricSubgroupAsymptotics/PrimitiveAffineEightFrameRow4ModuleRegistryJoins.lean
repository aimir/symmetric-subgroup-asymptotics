import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleRegistryJoin0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleRegistryJoin8

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameRow4TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 14) (c : Fin 14) :
    (PrimitiveAffineEightFrameRow4ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow4ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow4ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow4ModuleOrbits.cyclicRepresentative c) := by
  by_cases h0 : i.val < 8
  · let j : Fin 8 := ⟨i.val - 0, by omega⟩
    have hj : JoinChunk0.embed j = i := by
      apply Fin.ext
      simp [JoinChunk0.embed, j]
    rw [← hj]
    exact JoinChunk0.child_eq j c
  by_cases h8 : i.val < 14
  · let j : Fin 6 := ⟨i.val - 8, by omega⟩
    have hj : JoinChunk8.embed j = i := by
      apply Fin.ext
      simp [JoinChunk8.embed, j]
      omega
    rw [← hj]
    exact JoinChunk8.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow4ModuleRepresentation.states (0 : Fin 14)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow4ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow4ModuleRepresentation.charts (0 : Fin 14)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow4ModuleRepresentation.representation PrimitiveAffineEightFrameRow4ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow4ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow4ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow4ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow4ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow4ModuleOrbits.orbit_span_eq (0 : Fin 14) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleRegistry

end
