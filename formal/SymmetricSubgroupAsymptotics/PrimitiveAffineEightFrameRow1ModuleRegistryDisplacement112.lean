import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 112–119. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

local instance sourceGroupDisplacement112 : Group Source := PrimitiveAffineEightFrameRow1TopCertificate.group
local instance sourceInhabitedDisplacement112 : Inhabited Source := ⟨1⟩

namespace D112

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 258 else (if j.val < 4 then 513 else 1032))) else (if j.val < 7 then (if j.val < 6 then 2052 else 4138) else (if j.val < 8 then 8213 else (if j.val < 9 then 16416 else 32784))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 112).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 112).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 3 else (if j.val < 4 then 3 else 4))) else (if j.val < 7 then (if j.val < 6 then 3 else 3) else (if j.val < 8 then 6 else (if j.val < 9 then 1 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,1,1] else (if j.val < 4 then #[0,0,1] else #[0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,1] else #[0,0,1]) else (if j.val < 8 then #[0,0,0,0,1,1] else (if j.val < 9 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0]) else (if j.val < 3 then #[3,2,3] else (if j.val < 4 then #[2,3,2] else #[2,3,4,2]))) else (if j.val < 7 then (if j.val < 6 then #[2,5,3] else #[0,3,3]) else (if j.val < 8 then #[0,1,2,3,2,3] else (if j.val < 9 then #[9] else #[8,9]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 112).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 112).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 112) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D112

namespace D113

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 259 else (if j.val < 4 then 514 else 1036))) else (if j.val < 7 then (if j.val < 6 then 2056 else 4159) else (if j.val < 8 then 8234 else (if j.val < 9 then 16432 else 32800))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 113).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 113).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 3 else (if j.val < 4 then 3 else 4))) else (if j.val < 7 then (if j.val < 6 then 3 else 3) else (if j.val < 8 then 5 else (if j.val < 9 then 1 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,1,1] else (if j.val < 4 then #[0,0,1] else #[0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,1] else #[0,0,1]) else (if j.val < 8 then #[0,0,0,1,1] else (if j.val < 9 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0]) else (if j.val < 3 then #[3,2,3] else (if j.val < 4 then #[2,3,2] else #[2,3,4,2]))) else (if j.val < 7 then (if j.val < 6 then #[2,5,3] else #[1,3,3]) else (if j.val < 8 then #[0,2,3,2,3] else (if j.val < 9 then #[9] else #[8,9]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 113).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 113).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 113) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D113

namespace D114

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 284 else (if j.val < 4 then 550 else 1046))) else (if j.val < 7 then (if j.val < 6 then 2083 else 4148) else (if j.val < 8 then 8242 else (if j.val < 9 then 16446 else 32823))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 114).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 114).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 4 else (if j.val < 4 then 5 else 4))) else (if j.val < 7 then (if j.val < 6 then 3 else 3) else (if j.val < 8 then 5 else (if j.val < 9 then 2 else 3))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0,1,1] else (if j.val < 4 then #[0,0,0,0,1] else #[0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,1] else #[0,0,1]) else (if j.val < 8 then #[0,0,0,1,1] else (if j.val < 9 then #[0,0] else #[0,0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0]) else (if j.val < 3 then #[1,3,2,3] else (if j.val < 4 then #[0,1,2,3,2] else #[2,3,4,2]))) else (if j.val < 7 then (if j.val < 6 then #[2,5,3] else #[1,3,3]) else (if j.val < 8 then #[1,2,3,2,3] else (if j.val < 9 then #[0,9] else #[1,8,9]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 114).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 114).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 114) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D114

namespace D115

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 285 else (if j.val < 4 then 549 else 1042))) else (if j.val < 7 then (if j.val < 6 then 2095 else 4129) else (if j.val < 8 then 8205 else (if j.val < 9 then 16430 else 32775))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 115).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 115).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 4 else (if j.val < 4 then 5 else 4))) else (if j.val < 7 then (if j.val < 6 then 3 else 3) else (if j.val < 8 then 4 else (if j.val < 9 then 2 else 3))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0,1,1] else (if j.val < 4 then #[0,0,0,0,1] else #[0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,1] else #[0,0,1]) else (if j.val < 8 then #[0,0,1,1] else (if j.val < 9 then #[0,0] else #[0,0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0]) else (if j.val < 3 then #[1,3,2,3] else (if j.val < 4 then #[0,1,2,3,2] else #[2,3,4,2]))) else (if j.val < 7 then (if j.val < 6 then #[2,5,3] else #[0,3,3]) else (if j.val < 8 then #[2,3,2,3] else (if j.val < 9 then #[0,9] else #[1,8,9]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 115).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 115).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 115) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D115

namespace D116

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 287 else (if j.val < 4 then 548 else 1050))) else (if j.val < 7 then (if j.val < 6 then 2091 else 4107) else (if j.val < 8 then 8216 else (if j.val < 9 then 16398 else 32791))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 116).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 116).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 4 else (if j.val < 4 then 5 else 4))) else (if j.val < 7 then (if j.val < 6 then 3 else 2) else (if j.val < 8 then 6 else (if j.val < 9 then 2 else 3))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0,1,1] else (if j.val < 4 then #[0,0,0,0,1] else #[0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,1] else #[0,1]) else (if j.val < 8 then #[0,0,0,0,1,1] else (if j.val < 9 then #[0,0] else #[0,0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0]) else (if j.val < 3 then #[1,3,2,3] else (if j.val < 4 then #[0,1,2,3,2] else #[2,3,4,2]))) else (if j.val < 7 then (if j.val < 6 then #[2,5,3] else #[3,3]) else (if j.val < 8 then #[0,1,2,3,2,3] else (if j.val < 9 then #[0,9] else #[1,8,9]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 116).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 116).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 116) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D116

namespace D117

private def displacementBasis (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 30 else 39) else (if j.val < 3 then 75 else 141)) else (if j.val < 6 then (if j.val < 5 then 1285 else 6917) else (if j.val < 7 then 8709 else (if j.val < 8 then 19200 else 34821))))

private def displacementDual (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else 128)) else (if j.val < 6 then (if j.val < 5 then 1024 else 4096) else (if j.val < 7 then 8192 else (if j.val < 8 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 9 :=
  binaryCoordinateSpaceOfMasks 16 9
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 117).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 117).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 2) else (if j.val < 3 then 2 else 1)) else (if j.val < 6 then (if j.val < 5 then 1 else 5) else (if j.val < 7 then 2 else (if j.val < 8 then 2 else 7))))

private def generatorRows (j : Fin 9) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,0] else #[0,0]) else (if j.val < 3 then #[0,0] else #[0])) else (if j.val < 6 then (if j.val < 5 then #[3] else #[0,0,0,0,3]) else (if j.val < 7 then #[0,3] else (if j.val < 8 then #[0,0] else #[0,0,0,0,0,0,3]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 11) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,2] else #[1,4]) else (if j.val < 3 then #[0,4] else #[4])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[0,4,5,6,0]) else (if j.val < 7 then #[5,0] else (if j.val < 8 then #[6,10] else #[0,4,5,6,9,10,0]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 117).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 117).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 117) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D117

namespace D118

private def displacementBasis (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 30 else 39) else (if j.val < 3 then 75 else 141)) else (if j.val < 6 then (if j.val < 5 then 2570 else 5130) else (if j.val < 7 then 9984 else (if j.val < 8 then 16650 else 34570))))

private def displacementDual (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else 128)) else (if j.val < 6 then (if j.val < 5 then 2048 else 4096) else (if j.val < 7 then 8192 else (if j.val < 8 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 9 :=
  binaryCoordinateSpaceOfMasks 16 9
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 118).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 118).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 1) else (if j.val < 3 then 1 else 1)) else (if j.val < 6 then (if j.val < 5 then 1 else 5) else (if j.val < 7 then 3 else (if j.val < 8 then 5 else 5))))

private def generatorRows (j : Fin 9) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,0] else #[0]) else (if j.val < 3 then #[0] else #[0])) else (if j.val < 6 then (if j.val < 5 then #[3] else #[0,0,0,0,3]) else (if j.val < 7 then #[0,0,0] else (if j.val < 8 then #[0,0,0,0,3] else #[0,0,0,0,3]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 11) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,2,3] else #[1]) else (if j.val < 3 then #[0] else #[3])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[0,3,5,6,0]) else (if j.val < 7 then #[0,3,5] else (if j.val < 8 then #[0,3,6,10,0] else #[5,6,9,10,0]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 118).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 118).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 118) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D118

namespace D119

private def displacementBasis (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 30 else 39) else (if j.val < 3 then 75 else 141)) else (if j.val < 6 then (if j.val < 5 then 3855 else 4367) else (if j.val < 7 then 9984 else (if j.val < 8 then 17423 else 33295))))

private def displacementDual (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else 128)) else (if j.val < 6 then (if j.val < 5 then 2048 else 4096) else (if j.val < 7 then 8192 else (if j.val < 8 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 9 :=
  binaryCoordinateSpaceOfMasks 16 9
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 119).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 119).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 1 else 1)) else (if j.val < 6 then (if j.val < 5 then 1 else 3) else (if j.val < 7 then 3 else (if j.val < 8 then 5 else 7))))

private def generatorRows (j : Fin 9) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,0] else #[0,0,0]) else (if j.val < 3 then #[0] else #[0])) else (if j.val < 6 then (if j.val < 5 then #[3] else #[0,0,3]) else (if j.val < 7 then #[0,0,0] else (if j.val < 8 then #[0,0,0,0,3] else #[0,0,0,0,0,0,3]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 11) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,2,3] else #[0,1,3]) else (if j.val < 3 then #[3] else #[0])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[5,6,0]) else (if j.val < 7 then #[0,3,5] else (if j.val < 8 then #[0,3,6,10,0] else #[0,3,5,6,9,10,0]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 119).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 119).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 119) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D119

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

end
