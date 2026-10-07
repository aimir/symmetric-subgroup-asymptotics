import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleRegistryJoin0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleRegistryJoin16
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleRegistryJoin32
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleRegistryJoin48

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameRow2TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 49) (c : Fin 34) :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow2ModuleOrbits.cyclicRepresentative c) := by
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
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states (0 : Fin 49)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts (0 : Fin 49)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation PrimitiveAffineEightFrameRow2ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow2ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow2ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow2ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow2ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow2ModuleOrbits.orbit_span_eq (0 : Fin 49) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleRegistry

end
