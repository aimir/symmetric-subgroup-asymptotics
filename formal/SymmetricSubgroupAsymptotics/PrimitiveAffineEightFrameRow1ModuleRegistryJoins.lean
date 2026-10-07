import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoin0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoin8
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoin16
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoin24
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoin32
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoin40
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoin48
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoin56
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoin64
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoin72
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoin80
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoin88
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoin96
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoin104
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoin112
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoin120
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoin128
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoin136

/-! Assembly of the bounded invariant-state cyclic-join chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

local instance sourceGroupJoins : Group Source := PrimitiveAffineEightFrameRow1TopCertificate.group
local instance sourceInhabitedJoins : Inhabited Source := ⟨1⟩

theorem child_eq
    (i : Fin 143) (c : Fin 118) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states (child i c)).toSubmodule =
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states i).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow1ModuleOrbits.cyclicRepresentative c) := by
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
  by_cases h96 : i.val < 104
  · let j : Fin 8 := ⟨i.val - 96, by omega⟩
    have hj : JoinChunk96.embed j = i := by
      apply Fin.ext
      simp [JoinChunk96.embed, j]
      omega
    rw [← hj]
    exact JoinChunk96.child_eq j c
  by_cases h104 : i.val < 112
  · let j : Fin 8 := ⟨i.val - 104, by omega⟩
    have hj : JoinChunk104.embed j = i := by
      apply Fin.ext
      simp [JoinChunk104.embed, j]
      omega
    rw [← hj]
    exact JoinChunk104.child_eq j c
  by_cases h112 : i.val < 120
  · let j : Fin 8 := ⟨i.val - 112, by omega⟩
    have hj : JoinChunk112.embed j = i := by
      apply Fin.ext
      simp [JoinChunk112.embed, j]
      omega
    rw [← hj]
    exact JoinChunk112.child_eq j c
  by_cases h120 : i.val < 128
  · let j : Fin 8 := ⟨i.val - 120, by omega⟩
    have hj : JoinChunk120.embed j = i := by
      apply Fin.ext
      simp [JoinChunk120.embed, j]
      omega
    rw [← hj]
    exact JoinChunk120.child_eq j c
  by_cases h128 : i.val < 136
  · let j : Fin 8 := ⟨i.val - 128, by omega⟩
    have hj : JoinChunk128.embed j = i := by
      apply Fin.ext
      simp [JoinChunk128.embed, j]
      omega
    rw [← hj]
    exact JoinChunk128.child_eq j c
  by_cases h136 : i.val < 143
  · let j : Fin 7 := ⟨i.val - 136, by omega⟩
    have hj : JoinChunk136.embed j = i := by
      apply Fin.ext
      simp [JoinChunk136.embed, j]
      omega
    rw [← hj]
    exact JoinChunk136.child_eq j c
  omega

private theorem bottom_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states (0 : Fin 143)).toSubmodule = ⊥ := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts (0 : Fin 143)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1ModuleRepresentation.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    PrimitiveAffineEightFrameRow1ModuleOrbits.orbitRepresentative PrimitiveAffineEightFrameRow1ModuleOrbits.orbitCover
    PrimitiveAffineEightFrameRow1ModuleOrbits.cyclicRepresentative PrimitiveAffineEightFrameRow1ModuleOrbits.orbitCyclic
    PrimitiveAffineEightFrameRow1ModuleOrbits.orbit_span_eq (0 : Fin 143) bottom_eq child child_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

end
