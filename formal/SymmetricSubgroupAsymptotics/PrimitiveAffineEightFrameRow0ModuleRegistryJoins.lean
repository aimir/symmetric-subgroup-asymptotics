import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoin0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoin8
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoin16
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoin24
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoin32
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoin40
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoin48
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoin56
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoin64
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoin72
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoin80
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoin88
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoin96

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameRow0TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 101) (c : Fin 67) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow0ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow0ModuleOrbits.cyclicRepresentative c) := by
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
  by_cases h40 : i.val < 48
  · let j : Fin 8 := ⟨i.val - 40, by omega⟩
    have hj : JoinChunk40.embed j = i := by
      apply Fin.ext
      simp [JoinChunk40.embed, j]
      omega
    rw [← hj]
    exact JoinChunk40.child_eq j c
  by_cases h48 : i.val < 56
  · let j : Fin 8 := ⟨i.val - 48, by omega⟩
    have hj : JoinChunk48.embed j = i := by
      apply Fin.ext
      simp [JoinChunk48.embed, j]
      omega
    rw [← hj]
    exact JoinChunk48.child_eq j c
  by_cases h56 : i.val < 64
  · let j : Fin 8 := ⟨i.val - 56, by omega⟩
    have hj : JoinChunk56.embed j = i := by
      apply Fin.ext
      simp [JoinChunk56.embed, j]
      omega
    rw [← hj]
    exact JoinChunk56.child_eq j c
  by_cases h64 : i.val < 72
  · let j : Fin 8 := ⟨i.val - 64, by omega⟩
    have hj : JoinChunk64.embed j = i := by
      apply Fin.ext
      simp [JoinChunk64.embed, j]
      omega
    rw [← hj]
    exact JoinChunk64.child_eq j c
  by_cases h72 : i.val < 80
  · let j : Fin 8 := ⟨i.val - 72, by omega⟩
    have hj : JoinChunk72.embed j = i := by
      apply Fin.ext
      simp [JoinChunk72.embed, j]
      omega
    rw [← hj]
    exact JoinChunk72.child_eq j c
  by_cases h80 : i.val < 88
  · let j : Fin 8 := ⟨i.val - 80, by omega⟩
    have hj : JoinChunk80.embed j = i := by
      apply Fin.ext
      simp [JoinChunk80.embed, j]
      omega
    rw [← hj]
    exact JoinChunk80.child_eq j c
  by_cases h88 : i.val < 96
  · let j : Fin 8 := ⟨i.val - 88, by omega⟩
    have hj : JoinChunk88.embed j = i := by
      apply Fin.ext
      simp [JoinChunk88.embed, j]
      omega
    rw [← hj]
    exact JoinChunk88.child_eq j c
  by_cases h96 : i.val < 101
  · let j : Fin 5 := ⟨i.val - 96, by omega⟩
    have hj : JoinChunk96.embed j = i := by
      apply Fin.ext
      simp [JoinChunk96.embed, j]
      omega
    rw [← hj]
    exact JoinChunk96.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states (0 : Fin 101)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow0ModuleRepresentation.charts (0 : Fin 101)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow0ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow0ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow0ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow0ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow0ModuleOrbits.orbit_span_eq (0 : Fin 101) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

end
