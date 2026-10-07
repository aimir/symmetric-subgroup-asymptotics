import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleRegistryJoin0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleRegistryJoin8
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleRegistryJoin16
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleRegistryJoin24
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleRegistryJoin32
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleRegistryJoin40

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameRow8TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 43) (c : Fin 40) :
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow8ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow8ModuleOrbits.cyclicRepresentative c) := by
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
  by_cases h32 : i.val < 40
  · let j : Fin 8 := ⟨i.val - 32, by omega⟩
    have hj : JoinChunk32.embed j = i := by
      apply Fin.ext
      simp [JoinChunk32.embed, j]
      omega
    rw [← hj]
    exact JoinChunk32.child_eq j c
  by_cases h40 : i.val < 43
  · let j : Fin 3 := ⟨i.val - 40, by omega⟩
    have hj : JoinChunk40.embed j = i := by
      apply Fin.ext
      simp [JoinChunk40.embed, j]
      omega
    rw [← hj]
    exact JoinChunk40.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.states (0 : Fin 43)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow8ModuleRepresentation.charts (0 : Fin 43)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow8ModuleRepresentation.representation PrimitiveAffineEightFrameRow8ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow8ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow8ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow8ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow8ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow8ModuleOrbits.orbit_span_eq (0 : Fin 43) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleRegistry

end
