import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleRegistryJoin0

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameTop8TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 16) (c : Fin 14) :
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow13ModuleOrbits.cyclicRepresentative c) := by
  by_cases h0 : i.val < 16
  · let j : Fin 16 := ⟨i.val - 0, by omega⟩
    have hj : JoinChunk0.embed j = i := by
      apply Fin.ext
      simp [JoinChunk0.embed, j]
    rw [← hj]
    exact JoinChunk0.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states (0 : Fin 16)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts (0 : Fin 16)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow13ModuleRepresentation.representation PrimitiveAffineEightFrameRow13ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow13ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow13ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow13ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow13ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow13ModuleOrbits.orbit_span_eq (0 : Fin 16) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleRegistry

end
