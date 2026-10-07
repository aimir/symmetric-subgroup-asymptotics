import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21ModuleRegistryJoin0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21ModuleRegistryJoin16

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameRow21TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 27) (c : Fin 22) :
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow21ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow21ModuleOrbits.cyclicRepresentative c) := by
  by_cases h0 : i.val < 16
  · let j : Fin 16 := ⟨i.val - 0, by omega⟩
    have hj : JoinChunk0.embed j = i := by
      apply Fin.ext
      simp [JoinChunk0.embed, j]
    rw [← hj]
    exact JoinChunk0.child_eq j c
  by_cases h16 : i.val < 27
  · let j : Fin 11 := ⟨i.val - 16, by omega⟩
    have hj : JoinChunk16.embed j = i := by
      apply Fin.ext
      simp [JoinChunk16.embed, j]
      omega
    rw [← hj]
    exact JoinChunk16.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.states (0 : Fin 27)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow21ModuleRepresentation.charts (0 : Fin 27)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow21ModuleRepresentation.representation PrimitiveAffineEightFrameRow21ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow21ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow21ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow21ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow21ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow21ModuleOrbits.orbit_span_eq (0 : Fin 27) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21ModuleRegistry

end
