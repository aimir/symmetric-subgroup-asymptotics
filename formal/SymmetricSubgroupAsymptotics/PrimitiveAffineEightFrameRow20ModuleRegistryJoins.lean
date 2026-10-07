import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleRegistryJoin0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleRegistryJoin16
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleRegistryJoin32
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleRegistryJoin48

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameRow20TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 49) (c : Fin 40) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow20ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow20ModuleOrbits.cyclicRepresentative c) := by
  by_cases h0 : i.val < 16
  · let j : Fin 16 := ⟨i.val - 0, by omega⟩
    have hj : JoinChunk0.embed j = i := by
      apply Fin.ext
      simp [JoinChunk0.embed, j]
    rw [← hj]
    exact JoinChunk0.child_eq j c
  by_cases h16 : i.val < 32
  · let j : Fin 16 := ⟨i.val - 16, by omega⟩
    have hj : JoinChunk16.embed j = i := by
      apply Fin.ext
      simp [JoinChunk16.embed, j]
      omega
    rw [← hj]
    exact JoinChunk16.child_eq j c
  by_cases h32 : i.val < 48
  · let j : Fin 16 := ⟨i.val - 32, by omega⟩
    have hj : JoinChunk32.embed j = i := by
      apply Fin.ext
      simp [JoinChunk32.embed, j]
      omega
    rw [← hj]
    exact JoinChunk32.child_eq j c
  by_cases h48 : i.val < 49
  · let j : Fin 1 := ⟨i.val - 48, by omega⟩
    have hj : JoinChunk48.embed j = i := by
      apply Fin.ext
      simp [JoinChunk48.embed, j]
      omega
    rw [← hj]
    exact JoinChunk48.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states (0 : Fin 49)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow20ModuleRepresentation.charts (0 : Fin 49)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow20ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow20ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow20ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow20ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow20ModuleOrbits.orbit_span_eq (0 : Fin 49) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleRegistry

end
