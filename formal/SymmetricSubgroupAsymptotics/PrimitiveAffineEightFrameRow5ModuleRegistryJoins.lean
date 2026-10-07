import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRegistryJoin0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRegistryJoin8

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameRow5TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 14) (c : Fin 14) :
    (PrimitiveAffineEightFrameRow5ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow5ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow5ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow5ModuleOrbits.cyclicRepresentative c) := by
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
    (PrimitiveAffineEightFrameRow5ModuleRepresentation.states (0 : Fin 14)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow5ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow5ModuleRepresentation.charts (0 : Fin 14)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow5ModuleRepresentation.representation PrimitiveAffineEightFrameRow5ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow5ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow5ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow5ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow5ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow5ModuleOrbits.orbit_span_eq (0 : Fin 14) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRegistry

end
