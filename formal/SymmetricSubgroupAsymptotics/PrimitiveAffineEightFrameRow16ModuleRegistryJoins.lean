import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistryJoin0

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 7) (c : Fin 7) :
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow16ModuleOrbits.cyclicRepresentative c) := by
  by_cases h0 : i.val < 7
  · let j : Fin 7 := ⟨i.val - 0, by omega⟩
    have hj : JoinChunk0.embed j = i := by
      apply Fin.ext
      simp [JoinChunk0.embed, j]
    rw [← hj]
    exact JoinChunk0.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states (0 : Fin 7)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts (0 : Fin 7)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow16ModuleRepresentation.representation PrimitiveAffineEightFrameRow16ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow16ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow16ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow16ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow16ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow16ModuleOrbits.orbit_span_eq (0 : Fin 7) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistry

end
