import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistryJoin0

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 6) (c : Fin 6) :
    (PrimitiveAffineEightFrameRow15ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow15ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow15ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow15ModuleOrbits.cyclicRepresentative c) := by
  by_cases h0 : i.val < 6
  · let j : Fin 6 := ⟨i.val - 0, by omega⟩
    have hj : JoinChunk0.embed j = i := by
      apply Fin.ext
      simp [JoinChunk0.embed, j]
    rw [← hj]
    exact JoinChunk0.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow15ModuleRepresentation.states (0 : Fin 6)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow15ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow15ModuleRepresentation.charts (0 : Fin 6)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow15ModuleRepresentation.representation PrimitiveAffineEightFrameRow15ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow15ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow15ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow15ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow15ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow15ModuleOrbits.orbit_span_eq (0 : Fin 6) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistry

end
