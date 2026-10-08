import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistryJoin0

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameTop8TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 11) (c : Fin 11) :
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow12ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow12ModuleOrbits.cyclicRepresentative c) := by
  by_cases h0 : i.val < 11
  · let j : Fin 11 := ⟨i.val - 0, by omega⟩
    have hj : JoinChunk0.embed j = i := by
      apply Fin.ext
      simp [JoinChunk0.embed, j]
    rw [← hj]
    exact JoinChunk0.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states (0 : Fin 11)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts (0 : Fin 11)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow12ModuleRepresentation.representation PrimitiveAffineEightFrameRow12ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow12ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow12ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow12ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow12ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow12ModuleOrbits.orbit_span_eq (0 : Fin 11) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistry

end
