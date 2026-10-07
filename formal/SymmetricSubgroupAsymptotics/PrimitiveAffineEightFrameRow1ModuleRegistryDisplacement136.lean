import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 136–142. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

local instance sourceGroupDisplacement136 : Group Source := PrimitiveAffineEightFrameRow1TopCertificate.group
local instance sourceInhabitedDisplacement136 : Inhabited Source := ⟨1⟩

namespace D136

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 30 else (if j.val < 2 then 39 else 75)) else (if j.val < 4 then 141 else (if j.val < 5 then 257 else 515))) else (if j.val < 9 then (if j.val < 7 then 1028 else (if j.val < 8 then 2060 else 4107)) else (if j.val < 10 then 8198 else (if j.val < 11 then 16398 else 32777))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 16 else (if j.val < 2 then 32 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 136).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 136).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 3 else (if j.val < 2 then 2 else 2)) else (if j.val < 4 then 1 else (if j.val < 5 then 3 else 3))) else (if j.val < 9 then (if j.val < 7 then 5 else (if j.val < 8 then 4 else 4)) else (if j.val < 10 then 5 else (if j.val < 11 then 2 else 4))))

private def generatorRows (j : Fin 12) :
    Array (Fin 4) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0,0] else (if j.val < 2 then #[0,0] else #[0,0])) else (if j.val < 4 then #[0] else (if j.val < 5 then #[0,1,1] else #[0,0,1]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,0,0,1] else (if j.val < 8 then #[0,0,0,1] else #[0,0,0,1])) else (if j.val < 10 then #[0,0,0,1,1] else (if j.val < 11 then #[0,0] else #[0,0,0,0]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 13) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,1,2] else (if j.val < 2 then #[1,4] else #[0,4])) else (if j.val < 4 then #[4] else (if j.val < 5 then #[6,5,6] else #[5,6,5]))) else (if j.val < 9 then (if j.val < 7 then #[0,5,6,7,5] else (if j.val < 8 then #[0,5,8,6] else #[0,4,6,6])) else (if j.val < 10 then #[0,5,6,5,6] else (if j.val < 11 then #[0,12] else #[0,4,11,12]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 13 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 136).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 136).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 136) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D136

namespace D137

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 30 else (if j.val < 2 then 39 else 75)) else (if j.val < 4 then 141 else (if j.val < 5 then 259 else 514))) else (if j.val < 9 then (if j.val < 7 then 1036 else (if j.val < 8 then 2056 else 4102)) else (if j.val < 10 then 8205 else (if j.val < 11 then 16393 else 32775))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 16 else (if j.val < 2 then 32 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 137).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 137).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 3 else (if j.val < 2 then 1 else 1)) else (if j.val < 4 then 1 else (if j.val < 5 then 3 else 3))) else (if j.val < 9 then (if j.val < 7 then 5 else (if j.val < 8 then 4 else 4)) else (if j.val < 10 then 5 else (if j.val < 11 then 2 else 2))))

private def generatorRows (j : Fin 12) :
    Array (Fin 4) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0,0] else (if j.val < 2 then #[0] else #[0])) else (if j.val < 4 then #[0] else (if j.val < 5 then #[0,1,1] else #[0,0,1]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,0,0,1] else (if j.val < 8 then #[0,0,0,1] else #[0,0,0,1])) else (if j.val < 10 then #[0,0,0,1,1] else (if j.val < 11 then #[0,0] else #[0,0]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 13) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[1,2,3] else (if j.val < 2 then #[1] else #[0])) else (if j.val < 4 then #[3] else (if j.val < 5 then #[6,5,6] else #[5,6,5]))) else (if j.val < 9 then (if j.val < 7 then #[0,5,6,7,5] else (if j.val < 8 then #[0,5,8,6] else #[0,3,6,6])) else (if j.val < 10 then #[3,5,6,5,6] else (if j.val < 11 then #[3,12] else #[11,12]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 13 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 137).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 137).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 137) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D137

namespace D138

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 30 else (if j.val < 2 then 39 else 75)) else (if j.val < 4 then 141 else (if j.val < 5 then 258 else 513))) else (if j.val < 9 then (if j.val < 7 then 1032 else (if j.val < 8 then 2052 else 4109)) else (if j.val < 10 then 8203 else (if j.val < 11 then 16391 else 32782))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 16 else (if j.val < 2 then 32 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 138).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 138).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 3 else (if j.val < 2 then 3 else 1)) else (if j.val < 4 then 1 else (if j.val < 5 then 3 else 3))) else (if j.val < 9 then (if j.val < 7 then 5 else (if j.val < 8 then 3 else 3)) else (if j.val < 10 then 5 else (if j.val < 11 then 3 else 3))))

private def generatorRows (j : Fin 12) :
    Array (Fin 4) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0,0] else (if j.val < 2 then #[0,0,0] else #[0])) else (if j.val < 4 then #[0] else (if j.val < 5 then #[0,1,1] else #[0,0,1]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,0,0,1] else (if j.val < 8 then #[0,0,1] else #[0,0,1])) else (if j.val < 10 then #[0,0,0,1,1] else (if j.val < 11 then #[0,0,0] else #[0,0,0]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 13) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[1,2,3] else (if j.val < 2 then #[0,1,3] else #[3])) else (if j.val < 4 then #[0] else (if j.val < 5 then #[6,5,6] else #[5,6,5]))) else (if j.val < 9 then (if j.val < 7 then #[0,5,6,7,5] else (if j.val < 8 then #[5,8,6] else #[0,6,6])) else (if j.val < 10 then #[3,5,6,5,6] else (if j.val < 11 then #[0,3,12] else #[3,11,12]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 13 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 138).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 138).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 138) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D138

namespace D139

private def displacementBasis (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 27 else 34)) else (if j.val < 4 then 75 else (if j.val < 5 then 136 else 257))) else (if j.val < 9 then (if j.val < 7 then 515 else (if j.val < 8 then 1025 else 2057)) else (if j.val < 11 then (if j.val < 10 then 4107 else 8195) else (if j.val < 12 then 16395 else 32777))))

private def displacementDual (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 16 else 32)) else (if j.val < 4 then 64 else (if j.val < 5 then 128 else 256))) else (if j.val < 9 then (if j.val < 7 then 512 else (if j.val < 8 then 1024 else 2048)) else (if j.val < 11 then (if j.val < 10 then 4096 else 8192) else (if j.val < 12 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 13 :=
  binaryCoordinateSpaceOfMasks 16 13
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 139).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 139).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 7 else (if j.val < 2 then 7 else 7)) else (if j.val < 4 then 1 else (if j.val < 5 then 5 else 3))) else (if j.val < 9 then (if j.val < 7 then 3 else (if j.val < 8 then 6 else 4)) else (if j.val < 11 then (if j.val < 10 then 3 else 4) else (if j.val < 12 then 6 else 3))))

private def generatorRows (j : Fin 13) :
    Array (Fin 4) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0,0,0,1,1,3] else (if j.val < 2 then #[0,0,0,0,1,1,3] else #[0,0,0,0,1,1,3])) else (if j.val < 4 then #[0] else (if j.val < 5 then #[0,0,1,1,3] else #[0,1,1]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,1] else (if j.val < 8 then #[0,0,0,0,1,3] else #[0,0,1,3])) else (if j.val < 11 then (if j.val < 10 then #[0,0,1] else #[0,0,0,3]) else (if j.val < 12 then #[0,0,0,1,1,3] else #[0,0,0]))))

private def stateBasisRows (j : Fin 13) :
    Array (Fin 14) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,1,7,9,6,7,1] else (if j.val < 2 then #[2,3,7,9,6,7,1] else #[1,2,7,9,6,7,1])) else (if j.val < 4 then #[1] else (if j.val < 5 then #[7,9,6,7,1] else #[7,6,7]))) else (if j.val < 9 then (if j.val < 7 then #[6,7,6] else (if j.val < 8 then #[1,6,8,9,7,1] else #[6,7,6,1])) else (if j.val < 11 then (if j.val < 10 then #[1,7,7] else #[1,6,9,1]) else (if j.val < 12 then #[7,9,13,6,7,1] else #[1,12,13]))))

private def termGenerator (j : Fin 13)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 13)
    (t : Fin (termCount j)) : Fin 14 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 13)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 139).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 139).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 139) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D139

namespace D140

private def displacementBasis (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 15 else (if j.val < 2 then 17 else 39)) else (if j.val < 4 then 68 else (if j.val < 5 then 130 else 258))) else (if j.val < 9 then (if j.val < 7 then 513 else (if j.val < 8 then 1031 else 2052)) else (if j.val < 11 then (if j.val < 10 then 4098 else 8196) else (if j.val < 12 then 16391 else 32769))))

private def displacementDual (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 8 else (if j.val < 2 then 16 else 32)) else (if j.val < 4 then 64 else (if j.val < 5 then 128 else 256))) else (if j.val < 9 then (if j.val < 7 then 512 else (if j.val < 8 then 1024 else 2048)) else (if j.val < 11 then (if j.val < 10 then 4096 else 8192) else (if j.val < 12 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 13 :=
  binaryCoordinateSpaceOfMasks 16 13
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 140).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 140).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 7 else 2)) else (if j.val < 4 then 4 else (if j.val < 5 then 5 else 3))) else (if j.val < 9 then (if j.val < 7 then 3 else (if j.val < 8 then 4 else 4)) else (if j.val < 11 then (if j.val < 10 then 5 else 4) else (if j.val < 12 then 2 else 7))))

private def generatorRows (j : Fin 13) :
    Array (Fin 4) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0,0,1,3] else (if j.val < 2 then #[0,0,0,0,0,1,3] else #[0,0])) else (if j.val < 4 then #[0,0,1,3] else (if j.val < 5 then #[0,0,0,1,3] else #[0,1,1]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,1] else (if j.val < 8 then #[0,1,1,3] else #[0,0,0,1])) else (if j.val < 11 then (if j.val < 10 then #[0,0,0,0,3] else #[0,0,1,3]) else (if j.val < 12 then #[0,0] else #[0,0,0,0,0,1,3]))))

private def stateBasisRows (j : Fin 13) :
    Array (Fin 14) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[1,6,8,7,0] else (if j.val < 2 then #[0,2,3,6,8,7,0] else #[0,2])) else (if j.val < 4 then #[6,8,7,0] else (if j.val < 5 then #[0,6,8,7,0] else #[7,6,7]))) else (if j.val < 9 then (if j.val < 7 then #[6,7,6] else (if j.val < 8 then #[7,6,7,0] else #[0,6,9,7])) else (if j.val < 11 then (if j.val < 10 then #[0,6,7,8,0] else #[7,8,6,0]) else (if j.val < 12 then #[0,13] else #[0,6,8,12,13,7,0]))))

private def termGenerator (j : Fin 13)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 13)
    (t : Fin (termCount j)) : Fin 14 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 13)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 140).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 140).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 140) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D140

namespace D141

private def displacementBasis (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 10 else (if j.val < 2 then 20 else 39)) else (if j.val < 4 then 65 else (if j.val < 5 then 135 else 259))) else (if j.val < 9 then (if j.val < 7 then 514 else (if j.val < 8 then 1030 else 2050)) else (if j.val < 11 then (if j.val < 10 then 4102 else 8199) else (if j.val < 12 then 16387 else 32775))))

private def displacementDual (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 8 else (if j.val < 2 then 16 else 32)) else (if j.val < 4 then 64 else (if j.val < 5 then 128 else 256))) else (if j.val < 9 then (if j.val < 7 then 512 else (if j.val < 8 then 1024 else 2048)) else (if j.val < 11 then (if j.val < 10 then 4096 else 8192) else (if j.val < 12 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 13 :=
  binaryCoordinateSpaceOfMasks 16 13
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 141).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 141).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 6 else (if j.val < 2 then 6 else 2)) else (if j.val < 4 then 5 else (if j.val < 5 then 4 else 3))) else (if j.val < 9 then (if j.val < 7 then 3 else (if j.val < 8 then 4 else 4)) else (if j.val < 11 then (if j.val < 10 then 3 else 4) else (if j.val < 12 then 6 else 3))))

private def generatorRows (j : Fin 13) :
    Array (Fin 4) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0,0,0,1,3] else (if j.val < 2 then #[0,0,0,0,1,3] else #[0,0])) else (if j.val < 4 then #[0,0,0,1,3] else (if j.val < 5 then #[0,0,1,3] else #[0,1,1]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,1] else (if j.val < 8 then #[0,1,1,3] else #[0,0,0,3])) else (if j.val < 11 then (if j.val < 10 then #[0,0,1] else #[0,0,1,3]) else (if j.val < 12 then #[0,0,0,0,1,3] else #[0,0,0]))))

private def stateBasisRows (j : Fin 13) :
    Array (Fin 14) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,1,6,8,7,0] else (if j.val < 2 then #[2,3,6,8,7,0] else #[0,2])) else (if j.val < 4 then #[0,6,8,7,0] else (if j.val < 5 then #[6,8,7,0] else #[7,6,7]))) else (if j.val < 9 then (if j.val < 7 then #[6,7,6] else (if j.val < 8 then #[7,6,7,0] else #[0,8,9,0])) else (if j.val < 11 then (if j.val < 10 then #[0,7,7] else #[7,8,6,0]) else (if j.val < 12 then #[0,6,8,13,7,0] else #[0,12,13]))))

private def termGenerator (j : Fin 13)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 13)
    (t : Fin (termCount j)) : Fin 14 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 13)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 141).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 141).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 141) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D141

namespace D142

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
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 142).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 142).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 16) : ℕ :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 3 else 4)) else (if j.val < 6 then (if j.val < 5 then 2 else 1) else (if j.val < 7 then 4 else 2))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 3 else 3) else (if j.val < 11 then 4 else 3)) else (if j.val < 14 then (if j.val < 13 then 2 else 4) else (if j.val < 15 then 1 else 2))))

private def generatorRows (j : Fin 16) :
    Array (Fin 4) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,1] else #[0,1,1]) else (if j.val < 3 then #[0,0,1] else #[0,0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,0] else #[0]) else (if j.val < 7 then #[0,0,1,1] else #[0,1]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[0,1,1] else #[0,0,1]) else (if j.val < 11 then #[0,0,0,1] else #[0,0,1])) else (if j.val < 14 then (if j.val < 13 then #[0,1] else #[0,0,1,1]) else (if j.val < 15 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 16) :
    Array (Fin 16) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1] else #[0,0,1]) else (if j.val < 3 then #[1,2,0] else #[0,1,3,1])) else (if j.val < 6 then (if j.val < 5 then #[4,5] else #[4]) else (if j.val < 7 then #[0,1,0,1] else #[0,0]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[9,8,9] else #[8,9,8]) else (if j.val < 11 then #[8,9,10,8] else #[8,11,9])) else (if j.val < 14 then (if j.val < 13 then #[9,9] else #[8,9,8,9]) else (if j.val < 15 then #[15] else #[14,15]))))

private def termGenerator (j : Fin 16)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 16)
    (t : Fin (termCount j)) : Fin 16 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 16)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 142).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 142).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 142) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D142

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

end
