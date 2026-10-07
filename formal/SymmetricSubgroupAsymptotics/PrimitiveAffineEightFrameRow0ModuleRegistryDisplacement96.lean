import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 96–100. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

local instance sourceGroupDisplacement96 : Group Source := PrimitiveAffineEightFrameRow0TopCertificate.group
local instance sourceInhabitedDisplacement96 : Inhabited Source := ⟨1⟩

namespace D96

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 30 else (if j.val < 2 then 39 else 75)) else (if j.val < 4 then 141 else (if j.val < 5 then 257 else 514))) else (if j.val < 9 then (if j.val < 7 then 1028 else (if j.val < 8 then 2056 else 4110)) else (if j.val < 10 then 8199 else (if j.val < 11 then 16395 else 32781))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 16 else (if j.val < 2 then 32 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 96).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 96).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 1 else 1)) else (if j.val < 4 then 3 else (if j.val < 5 then 3 else 3))) else (if j.val < 9 then (if j.val < 7 then 5 else (if j.val < 8 then 3 else 3)) else (if j.val < 10 then 5 else (if j.val < 11 then 1 else 3))))

private def generatorRows (j : Fin 12) :
    Array (Fin 4) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0] else #[0])) else (if j.val < 4 then #[0,0,0] else (if j.val < 5 then #[0,1,1] else #[0,0,1]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,0,0,1] else (if j.val < 8 then #[0,0,1] else #[0,0,1])) else (if j.val < 10 then #[0,0,0,1,1] else (if j.val < 11 then #[0] else #[0,0,0]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 13) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[2] else (if j.val < 2 then #[0] else #[4])) else (if j.val < 4 then #[2,3,4] else (if j.val < 5 then #[6,5,6] else #[5,6,5]))) else (if j.val < 9 then (if j.val < 7 then #[0,5,6,7,5] else (if j.val < 8 then #[5,8,6] else #[2,6,6])) else (if j.val < 10 then #[0,5,6,5,6] else (if j.val < 11 then #[12] else #[2,11,12]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 13 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 96).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 96).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 96) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D96

namespace D97

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 30 else (if j.val < 2 then 39 else 75)) else (if j.val < 4 then 141 else (if j.val < 5 then 257 else 514))) else (if j.val < 9 then (if j.val < 7 then 1028 else (if j.val < 8 then 2056 else 4110)) else (if j.val < 10 then 8199 else (if j.val < 11 then 16395 else 32781))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 16 else (if j.val < 2 then 32 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 97).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 97).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 2)) else (if j.val < 4 then 3 else (if j.val < 5 then 3 else 3))) else (if j.val < 9 then (if j.val < 7 then 4 else (if j.val < 8 then 4 else 3)) else (if j.val < 10 then 6 else (if j.val < 11 then 2 else 3))))

private def generatorRows (j : Fin 12) :
    Array (Fin 4) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,0] else #[0,0])) else (if j.val < 4 then #[0,0,0] else (if j.val < 5 then #[0,1,1] else #[0,0,1]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,0,1] else (if j.val < 8 then #[0,0,0,1] else #[0,0,1])) else (if j.val < 10 then #[0,0,0,0,1,1] else (if j.val < 11 then #[0,0] else #[0,0,0]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 13) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[1] else (if j.val < 2 then #[0,1] else #[1,4])) else (if j.val < 4 then #[0,3,4] else (if j.val < 5 then #[6,5,6] else #[5,6,5]))) else (if j.val < 9 then (if j.val < 7 then #[5,6,7,5] else (if j.val < 8 then #[0,5,8,6] else #[1,6,6])) else (if j.val < 10 then #[0,1,5,6,5,6] else (if j.val < 11 then #[1,12] else #[0,11,12]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 13 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 97).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 97).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 97) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D97

namespace D98

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 30 else (if j.val < 2 then 39 else 75)) else (if j.val < 4 then 141 else (if j.val < 5 then 257 else 514))) else (if j.val < 9 then (if j.val < 7 then 1028 else (if j.val < 8 then 2056 else 4110)) else (if j.val < 10 then 8199 else (if j.val < 11 then 16395 else 32781))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 16 else (if j.val < 2 then 32 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 98).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 98).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 2)) else (if j.val < 4 then 3 else (if j.val < 5 then 3 else 3))) else (if j.val < 9 then (if j.val < 7 then 4 else (if j.val < 8 then 4 else 3)) else (if j.val < 10 then 6 else (if j.val < 11 then 2 else 3))))

private def generatorRows (j : Fin 12) :
    Array (Fin 4) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,0] else #[0,0])) else (if j.val < 4 then #[0,0,0] else (if j.val < 5 then #[0,1,1] else #[0,0,1]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,0,1] else (if j.val < 8 then #[0,0,0,1] else #[0,0,1])) else (if j.val < 10 then #[0,0,0,0,1,1] else (if j.val < 11 then #[0,0] else #[0,0,0]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 13) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,1] else #[1,4])) else (if j.val < 4 then #[1,3,4] else (if j.val < 5 then #[6,5,6] else #[5,6,5]))) else (if j.val < 9 then (if j.val < 7 then #[5,6,7,5] else (if j.val < 8 then #[0,5,8,6] else #[0,6,6])) else (if j.val < 10 then #[0,1,5,6,5,6] else (if j.val < 11 then #[1,12] else #[1,11,12]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 13 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 98).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 98).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 98) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D98

namespace D99

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 30 else (if j.val < 2 then 39 else 75)) else (if j.val < 4 then 141 else (if j.val < 5 then 257 else 514))) else (if j.val < 9 then (if j.val < 7 then 1028 else (if j.val < 8 then 2056 else 4110)) else (if j.val < 10 then 8199 else (if j.val < 11 then 16395 else 32781))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 16 else (if j.val < 2 then 32 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 99).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 99).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 2)) else (if j.val < 4 then 4 else (if j.val < 5 then 3 else 3))) else (if j.val < 9 then (if j.val < 7 then 5 else (if j.val < 8 then 4 else 4)) else (if j.val < 10 then 5 else (if j.val < 11 then 2 else 4))))

private def generatorRows (j : Fin 12) :
    Array (Fin 4) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,0])) else (if j.val < 4 then #[0,0,0,0] else (if j.val < 5 then #[0,1,1] else #[0,0,1]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,0,0,1] else (if j.val < 8 then #[0,0,0,1] else #[0,0,0,1])) else (if j.val < 10 then #[0,0,0,1,1] else (if j.val < 11 then #[0,0] else #[0,0,0,0]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 14) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0] else #[1,5])) else (if j.val < 4 then #[0,1,4,5] else (if j.val < 5 then #[7,6,7] else #[6,7,6]))) else (if j.val < 9 then (if j.val < 7 then #[0,6,7,8,6] else (if j.val < 8 then #[1,6,9,7] else #[0,1,7,7])) else (if j.val < 10 then #[0,6,7,6,7] else (if j.val < 11 then #[1,13] else #[0,1,12,13]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 14 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 99).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 99).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 99) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D99

namespace D100

private def displacementBasis (j : Fin 16) : ℕ :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 4 else 8)) else (if j.val < 6 then (if j.val < 5 then 16 else 32) else (if j.val < 7 then 64 else 128))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 256 else 512) else (if j.val < 11 then 1024 else 2048)) else (if j.val < 14 then (if j.val < 13 then 4096 else 8192) else (if j.val < 15 then 16384 else 32768))))

private def displacementDual (j : Fin 16) : ℕ :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 4 else 8)) else (if j.val < 6 then (if j.val < 5 then 16 else 32) else (if j.val < 7 then 64 else 128))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 256 else 512) else (if j.val < 11 then 1024 else 2048)) else (if j.val < 14 then (if j.val < 13 then 4096 else 8192) else (if j.val < 15 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 16 :=
  binaryCoordinateSpaceOfMasks 16 16
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 100).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 100).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 16) : ℕ :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 4 else 3)) else (if j.val < 6 then (if j.val < 5 then 2 else 4) else (if j.val < 7 then 1 else 2))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 3 else 3) else (if j.val < 11 then 4 else 3)) else (if j.val < 14 then (if j.val < 13 then 2 else 4) else (if j.val < 15 then 1 else 2))))

private def generatorRows (j : Fin 16) :
    Array (Fin 4) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1] else #[0,0,1]) else (if j.val < 3 then #[0,0,0,1] else #[0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1] else #[0,0,1,1]) else (if j.val < 7 then #[0] else #[0,0]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[0,1,1] else #[0,0,1]) else (if j.val < 11 then #[0,0,0,1] else #[0,0,1])) else (if j.val < 14 then (if j.val < 13 then #[0,1] else #[0,0,1,1]) else (if j.val < 15 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 16) :
    Array (Fin 16) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,0,1] else #[0,1,0]) else (if j.val < 3 then #[0,1,2,0] else #[0,3,1])) else (if j.val < 6 then (if j.val < 5 then #[1,1] else #[0,1,0,1]) else (if j.val < 7 then #[7] else #[6,7]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[9,8,9] else #[8,9,8]) else (if j.val < 11 then #[8,9,10,8] else #[8,11,9])) else (if j.val < 14 then (if j.val < 13 then #[9,9] else #[8,9,8,9]) else (if j.val < 15 then #[15] else #[14,15]))))

private def termGenerator (j : Fin 16)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 16)
    (t : Fin (termCount j)) : Fin 16 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 16)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 100).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 100).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 100) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D100

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

end
