import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistryJoin0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistryJoin16
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistryJoin32
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistryJoin48
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistryJoin64
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistryJoin80

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameRow3TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 83) (c : Fin 58) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow3ModuleOrbits.cyclicRepresentative c) := by
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
  by_cases h48 : i.val < 64
  · let j : Fin 16 := ⟨i.val - 48, by omega⟩
    have hj : JoinChunk48.embed j = i := by
      apply Fin.ext
      simp [JoinChunk48.embed, j]
      omega
    rw [← hj]
    exact JoinChunk48.child_eq j c
  by_cases h64 : i.val < 80
  · let j : Fin 16 := ⟨i.val - 64, by omega⟩
    have hj : JoinChunk64.embed j = i := by
      apply Fin.ext
      simp [JoinChunk64.embed, j]
      omega
    rw [← hj]
    exact JoinChunk64.child_eq j c
  by_cases h80 : i.val < 83
  · let j : Fin 3 := ⟨i.val - 80, by omega⟩
    have hj : JoinChunk80.embed j = i := by
      apply Fin.ext
      simp [JoinChunk80.embed, j]
      omega
    rw [← hj]
    exact JoinChunk80.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states (0 : Fin 83)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts (0 : Fin 83)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow3ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow3ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow3ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow3ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow3ModuleOrbits.orbit_span_eq (0 : Fin 83) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistry

end
