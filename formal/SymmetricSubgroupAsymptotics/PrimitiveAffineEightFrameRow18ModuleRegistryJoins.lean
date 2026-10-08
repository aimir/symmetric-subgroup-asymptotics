import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleRegistryJoin0

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameTop10TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 5) (c : Fin 5) :
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow18ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow18ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow18ModuleOrbits.cyclicRepresentative c) := by
  by_cases h0 : i.val < 5
  · let j : Fin 5 := ⟨i.val - 0, by omega⟩
    have hj : JoinChunk0.embed j = i := by
      apply Fin.ext
      simp [JoinChunk0.embed, j]
    rw [← hj]
    exact JoinChunk0.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.states (0 : Fin 5)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow18ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow18ModuleRepresentation.charts (0 : Fin 5)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow18ModuleRepresentation.representation PrimitiveAffineEightFrameRow18ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow18ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow18ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow18ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow18ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow18ModuleOrbits.orbit_span_eq (0 : Fin 5) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleRegistry

end
