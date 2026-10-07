import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleRegistryJoin0

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameRow29TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 5) (c : Fin 5) :
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow29ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow29ModuleOrbits.cyclicRepresentative c) := by
  by_cases h0 : i.val < 5
  · let j : Fin 5 := ⟨i.val - 0, by omega⟩
    have hj : JoinChunk0.embed j = i := by
      apply Fin.ext
      simp [JoinChunk0.embed, j]
    rw [← hj]
    exact JoinChunk0.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states (0 : Fin 5)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts (0 : Fin 5)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow29ModuleRepresentation.representation PrimitiveAffineEightFrameRow29ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow29ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow29ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow29ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow29ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow29ModuleOrbits.orbit_span_eq (0 : Fin 5) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleRegistry

end
