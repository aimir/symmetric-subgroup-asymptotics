import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryJoin0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryJoin8
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryJoin16

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameRow6TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 17) (c : Fin 17) :
    (PrimitiveAffineEightFrameRow6ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow6ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow6ModuleOrbits.cyclicRepresentative c) := by
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
  by_cases h16 : i.val < 17
  · let j : Fin 1 := ⟨i.val - 16, by omega⟩
    have hj : JoinChunk16.embed j = i := by
      apply Fin.ext
      simp [JoinChunk16.embed, j]
      omega
    rw [← hj]
    exact JoinChunk16.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow6ModuleRepresentation.states (0 : Fin 17)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow6ModuleRepresentation.charts (0 : Fin 17)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow6ModuleRepresentation.representation PrimitiveAffineEightFrameRow6ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow6ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow6ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow6ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow6ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow6ModuleOrbits.orbit_span_eq (0 : Fin 17) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistry

end
