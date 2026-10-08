import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistryJoin0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistryJoin8
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistryJoin16

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameTop15TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 17) (c : Fin 17) :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow24ModuleOrbits.cyclicRepresentative c) := by
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
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states (0 : Fin 17)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts (0 : Fin 17)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow24ModuleRepresentation.representation PrimitiveAffineEightFrameRow24ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow24ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow24ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow24ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow24ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow24ModuleOrbits.orbit_span_eq (0 : Fin 17) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistry

end
