import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryJoin0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryJoin8
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryJoin16
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryJoin24

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameRow9TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 25) (c : Fin 22) :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow9ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow9ModuleOrbits.cyclicRepresentative c) := by
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
  by_cases h24 : i.val < 25
  · let j : Fin 1 := ⟨i.val - 24, by omega⟩
    have hj : JoinChunk24.embed j = i := by
      apply Fin.ext
      simp [JoinChunk24.embed, j]
      omega
    rw [← hj]
    exact JoinChunk24.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states (0 : Fin 25)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow9ModuleRepresentation.charts (0 : Fin 25)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow9ModuleRepresentation.representation PrimitiveAffineEightFrameRow9ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow9ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow9ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow9ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow9ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow9ModuleOrbits.orbit_span_eq (0 : Fin 25) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistry

end
