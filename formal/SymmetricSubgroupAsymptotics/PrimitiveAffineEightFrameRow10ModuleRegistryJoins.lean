import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow10ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow10ModuleRegistryJoin0

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow10ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameTop8TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 10) (c : Fin 10) :
    (PrimitiveAffineEightFrameRow10ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow10ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow10ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow10ModuleOrbits.cyclicRepresentative c) := by
  by_cases h0 : i.val < 10
  · let j : Fin 10 := ⟨i.val - 0, by omega⟩
    have hj : JoinChunk0.embed j = i := by
      apply Fin.ext
      simp [JoinChunk0.embed, j]
    rw [← hj]
    exact JoinChunk0.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow10ModuleRepresentation.states (0 : Fin 10)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow10ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow10ModuleRepresentation.charts (0 : Fin 10)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow10ModuleRepresentation.representation PrimitiveAffineEightFrameRow10ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow10ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow10ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow10ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow10ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow10ModuleOrbits.orbit_span_eq (0 : Fin 10) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow10ModuleRegistry

end
