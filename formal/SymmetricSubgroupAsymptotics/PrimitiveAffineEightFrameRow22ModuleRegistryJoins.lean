import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistryJoin0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistryJoin8
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistryJoin16

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameTop13TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 23) (c : Fin 19) :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow22ModuleOrbits.cyclicRepresentative c) := by
  by_cases h0 : i.val < 8
  · let j : Fin 8 := ⟨i.val - 0, by omega⟩
    have hj : JoinChunk0.embed j = i := by
      apply Fin.ext
      simp [JoinChunk0.embed, j]
    rw [← hj]
    exact JoinChunk0.child_eq j c
  by_cases h8 : i.val < 16
  · let j : Fin 8 := ⟨i.val - 8, by omega⟩
    have hj : JoinChunk8.embed j = i := by
      apply Fin.ext
      simp [JoinChunk8.embed, j]
      omega
    rw [← hj]
    exact JoinChunk8.child_eq j c
  by_cases h16 : i.val < 23
  · let j : Fin 7 := ⟨i.val - 16, by omega⟩
    have hj : JoinChunk16.embed j = i := by
      apply Fin.ext
      simp [JoinChunk16.embed, j]
      omega
    rw [← hj]
    exact JoinChunk16.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states (0 : Fin 23)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts (0 : Fin 23)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation PrimitiveAffineEightFrameRow22ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow22ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow22ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow22ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow22ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow22ModuleOrbits.orbit_span_eq (0 : Fin 23) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistry

end
