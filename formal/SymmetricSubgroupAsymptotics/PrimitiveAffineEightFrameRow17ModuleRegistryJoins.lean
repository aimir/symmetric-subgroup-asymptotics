import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistryJoin0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistryJoin8

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 12) (c : Fin 12) :
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow17ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow17ModuleOrbits.cyclicRepresentative c) := by
  by_cases h0 : i.val < 8
  · let j : Fin 8 := ⟨i.val - 0, by omega⟩
    have hj : JoinChunk0.embed j = i := by
      apply Fin.ext
      simp [JoinChunk0.embed, j]
    rw [← hj]
    exact JoinChunk0.child_eq j c
  by_cases h8 : i.val < 12
  · let j : Fin 4 := ⟨i.val - 8, by omega⟩
    have hj : JoinChunk8.embed j = i := by
      apply Fin.ext
      simp [JoinChunk8.embed, j]
      omega
    rw [← hj]
    exact JoinChunk8.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.states (0 : Fin 12)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow17ModuleRepresentation.charts (0 : Fin 12)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow17ModuleRepresentation.representation PrimitiveAffineEightFrameRow17ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow17ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow17ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow17ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow17ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow17ModuleOrbits.orbit_span_eq (0 : Fin 12) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistry

end
