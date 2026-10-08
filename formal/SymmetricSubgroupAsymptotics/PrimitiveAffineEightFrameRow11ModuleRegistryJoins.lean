import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow11ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow11ModuleRegistryJoin0

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow11ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameTop8TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 10) (c : Fin 10) :
    (PrimitiveAffineEightFrameRow11ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow11ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow11ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow11ModuleOrbits.cyclicRepresentative c) := by
  by_cases h0 : i.val < 10
  · let j : Fin 10 := ⟨i.val - 0, by omega⟩
    have hj : JoinChunk0.embed j = i := by
      apply Fin.ext
      simp [JoinChunk0.embed, j]
    rw [← hj]
    exact JoinChunk0.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow11ModuleRepresentation.states (0 : Fin 10)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow11ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow11ModuleRepresentation.charts (0 : Fin 10)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow11ModuleRepresentation.representation PrimitiveAffineEightFrameRow11ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow11ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow11ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow11ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow11ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow11ModuleOrbits.orbit_span_eq (0 : Fin 10) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow11ModuleRegistry

end
