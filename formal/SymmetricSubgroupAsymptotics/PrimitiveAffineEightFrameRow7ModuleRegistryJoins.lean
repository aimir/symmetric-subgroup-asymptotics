import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleRegistryJoin0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleRegistryJoin8
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleRegistryJoin16
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleRegistryJoin24

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameRow7TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 32) (c : Fin 22) :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow7ModuleOrbits.cyclicRepresentative c) := by
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
  by_cases h16 : i.val < 24
  · let j : Fin 8 := ⟨i.val - 16, by omega⟩
    have hj : JoinChunk16.embed j = i := by
      apply Fin.ext
      simp [JoinChunk16.embed, j]
      omega
    rw [← hj]
    exact JoinChunk16.child_eq j c
  by_cases h24 : i.val < 32
  · let j : Fin 8 := ⟨i.val - 24, by omega⟩
    have hj : JoinChunk24.embed j = i := by
      apply Fin.ext
      simp [JoinChunk24.embed, j]
      omega
    rw [← hj]
    exact JoinChunk24.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states (0 : Fin 32)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts (0 : Fin 32)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation PrimitiveAffineEightFrameRow7ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow7ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow7ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow7ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow7ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow7ModuleOrbits.orbit_span_eq (0 : Fin 32) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleRegistry

end
