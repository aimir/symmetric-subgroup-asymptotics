import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistryJoin0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistryJoin8

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameTop17TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 15) (c : Fin 15) :
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow26ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow26ModuleOrbits.cyclicRepresentative c) := by
  by_cases h0 : i.val < 8
  · let j : Fin 8 := ⟨i.val - 0, by omega⟩
    have hj : JoinChunk0.embed j = i := by
      apply Fin.ext
      simp [JoinChunk0.embed, j]
    rw [← hj]
    exact JoinChunk0.child_eq j c
  by_cases h8 : i.val < 15
  · let j : Fin 7 := ⟨i.val - 8, by omega⟩
    have hj : JoinChunk8.embed j = i := by
      apply Fin.ext
      simp [JoinChunk8.embed, j]
      omega
    rw [← hj]
    exact JoinChunk8.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states (0 : Fin 15)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow26ModuleRepresentation.charts (0 : Fin 15)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow26ModuleRepresentation.representation PrimitiveAffineEightFrameRow26ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow26ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow26ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow26ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow26ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow26ModuleOrbits.orbit_span_eq (0 : Fin 15) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistry

end
