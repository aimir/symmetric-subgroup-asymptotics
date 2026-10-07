import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 8–13. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRegistry

local instance sourceGroupDisplacement8 : Group Source := PrimitiveAffineEightFrameRow5TopCertificate.group
local instance sourceInhabitedDisplacement8 : Inhabited Source := ⟨1⟩

namespace D8

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 30 else 39) else (if j.val < 3 then 75 else (if j.val < 4 then 141 else 1285))) else (if j.val < 7 then (if j.val < 6 then 2570 else 4367) else (if j.val < 8 then 8709 else (if j.val < 9 then 16650 else 33295))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else (if j.val < 4 then 128 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow5ModuleRepresentation.states 8).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow5ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow5ModuleRepresentation.charts 8).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else (if j.val < 4 then 3 else 2))) else (if j.val < 7 then (if j.val < 6 then 4 else 2) else (if j.val < 8 then 3 else (if j.val < 9 then 3 else 3))))

private def generatorRows (j : Fin 10) :
    Array (Fin 7) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[3] else #[3,3]) else (if j.val < 3 then #[0,0,3] else (if j.val < 4 then #[0,3,3] else #[0,3]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,3,3] else #[0,3]) else (if j.val < 8 then #[0,0,3] else (if j.val < 9 then #[0,3,3] else #[0,0,3]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[2,3,1] else (if j.val < 4 then #[2,0,1] else #[5,1]))) else (if j.val < 7 then (if j.val < 6 then #[4,5,0,1] else #[7,0]) else (if j.val < 8 then #[6,7,1] else (if j.val < 9 then #[9,0,1] else #[8,9,0]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow5ModuleRepresentation.states 8).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow5ModuleRepresentation.charts 8).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow5ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow5ModuleRepresentation.representation PrimitiveAffineEightFrameRow5TopCertificate.ambient
      (PrimitiveAffineEightFrameRow5ModuleRepresentation.states 8) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D8

namespace D9

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 10 else 17)) else (if j.val < 4 then 34 else (if j.val < 5 then 65 else 130))) else (if j.val < 9 then (if j.val < 7 then 1280 else (if j.val < 8 then 2560 else 4352)) else (if j.val < 10 then 8704 else (if j.val < 11 then 16640 else 33280))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 8 else 16)) else (if j.val < 4 then 32 else (if j.val < 5 then 64 else 128))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow5ModuleRepresentation.states 9).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow5ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow5ModuleRepresentation.charts 9).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 3)) else (if j.val < 4 then 3 else (if j.val < 5 then 5 else 3))) else (if j.val < 9 then (if j.val < 7 then 1 else (if j.val < 8 then 2 else 1)) else (if j.val < 10 then 2 else (if j.val < 11 then 1 else 2))))

private def generatorRows (j : Fin 12) :
    Array (Fin 7) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[3] else (if j.val < 2 then #[3,3] else #[0,3,3])) else (if j.val < 4 then #[0,0,3] else (if j.val < 5 then #[0,0,0,0,3] else #[0,0,3]))) else (if j.val < 9 then (if j.val < 7 then #[0] else (if j.val < 8 then #[0,0] else #[0])) else (if j.val < 10 then #[0,0] else (if j.val < 11 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 12) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[1] else (if j.val < 2 then #[0,1] else #[1,0,1])) else (if j.val < 4 then #[0,1,0] else (if j.val < 5 then #[0,1,4,5,0] else #[0,4,1]))) else (if j.val < 9 then (if j.val < 7 then #[7] else (if j.val < 8 then #[6,7] else #[9])) else (if j.val < 10 then #[8,9] else (if j.val < 11 then #[11] else #[10,11]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow5ModuleRepresentation.states 9).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow5ModuleRepresentation.charts 9).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow5ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow5ModuleRepresentation.representation PrimitiveAffineEightFrameRow5TopCertificate.ambient
      (PrimitiveAffineEightFrameRow5ModuleRepresentation.states 9) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D9

namespace D10

private def displacementBasis (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 10 else 17)) else (if j.val < 5 then (if j.val < 4 then 34 else 65) else (if j.val < 6 then 130 else 257))) else (if j.val < 10 then (if j.val < 8 then 515 else (if j.val < 9 then 1025 else 2051)) else (if j.val < 12 then (if j.val < 11 then 4097 else 8195) else (if j.val < 13 then 16385 else 32771))))

private def displacementDual (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 8 else 16)) else (if j.val < 5 then (if j.val < 4 then 32 else 64) else (if j.val < 6 then 128 else 256))) else (if j.val < 10 then (if j.val < 8 then 512 else (if j.val < 9 then 1024 else 2048)) else (if j.val < 12 then (if j.val < 11 then 4096 else 8192) else (if j.val < 13 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 14 :=
  binaryCoordinateSpaceOfMasks 16 14
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow5ModuleRepresentation.states 10).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow5ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow5ModuleRepresentation.charts 10).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 2 else 1)) else (if j.val < 5 then (if j.val < 4 then 2 else 4) else (if j.val < 6 then 2 else 3))) else (if j.val < 10 then (if j.val < 8 then 3 else (if j.val < 9 then 3 else 3)) else (if j.val < 12 then (if j.val < 11 then 3 else 3) else (if j.val < 13 then 3 else 3))))

private def generatorRows (j : Fin 14) :
    Array (Fin 7) :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0,1] else #[1])) else (if j.val < 5 then (if j.val < 4 then #[1,1] else #[0,0,1,1]) else (if j.val < 6 then #[0,1] else #[0,1,1]))) else (if j.val < 10 then (if j.val < 8 then #[0,0,1] else (if j.val < 9 then #[0,1,1] else #[0,0,1])) else (if j.val < 12 then (if j.val < 11 then #[0,1,1] else #[0,0,1]) else (if j.val < 13 then #[0,1,1] else #[0,0,1]))))

private def stateBasisRows (j : Fin 14) :
    Array (Fin 14) :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then #[0,7] else (if j.val < 2 then #[1,6] else #[6])) else (if j.val < 5 then (if j.val < 4 then #[6,7] else #[4,5,6,7]) else (if j.val < 6 then #[4,7] else #[7,6,7]))) else (if j.val < 10 then (if j.val < 8 then #[6,7,6] else (if j.val < 9 then #[9,6,7] else #[8,9,6])) else (if j.val < 12 then (if j.val < 11 then #[11,6,7] else #[10,11,6]) else (if j.val < 13 then #[13,6,7] else #[12,13,6]))))

private def termGenerator (j : Fin 14)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 14)
    (t : Fin (termCount j)) : Fin 14 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 14)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow5ModuleRepresentation.states 10).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow5ModuleRepresentation.charts 10).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow5ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow5ModuleRepresentation.representation PrimitiveAffineEightFrameRow5TopCertificate.ambient
      (PrimitiveAffineEightFrameRow5ModuleRepresentation.states 10) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D10

namespace D11

private def displacementBasis (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 10 else 17)) else (if j.val < 5 then (if j.val < 4 then 34 else 65) else (if j.val < 6 then 130 else 258))) else (if j.val < 10 then (if j.val < 8 then 513 else (if j.val < 9 then 1026 else 2049)) else (if j.val < 12 then (if j.val < 11 then 4098 else 8193) else (if j.val < 13 then 16386 else 32769))))

private def displacementDual (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 8 else 16)) else (if j.val < 5 then (if j.val < 4 then 32 else 64) else (if j.val < 6 then 128 else 256))) else (if j.val < 10 then (if j.val < 8 then 512 else (if j.val < 9 then 1024 else 2048)) else (if j.val < 12 then (if j.val < 11 then 4096 else 8192) else (if j.val < 13 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 14 :=
  binaryCoordinateSpaceOfMasks 16 14
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow5ModuleRepresentation.states 11).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow5ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow5ModuleRepresentation.charts 11).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 3 else (if j.val < 2 then 2 else 1)) else (if j.val < 5 then (if j.val < 4 then 1 else 3) else (if j.val < 6 then 3 else 3))) else (if j.val < 10 then (if j.val < 8 then 3 else (if j.val < 9 then 3 else 3)) else (if j.val < 12 then (if j.val < 11 then 3 else 3) else (if j.val < 13 then 3 else 3))))

private def generatorRows (j : Fin 14) :
    Array (Fin 7) :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then #[0,1,1] else (if j.val < 2 then #[0,1] else #[1])) else (if j.val < 5 then (if j.val < 4 then #[1] else #[0,0,1]) else (if j.val < 6 then #[0,1,1] else #[0,1,1]))) else (if j.val < 10 then (if j.val < 8 then #[0,0,1] else (if j.val < 9 then #[0,1,1] else #[0,0,1])) else (if j.val < 12 then (if j.val < 11 then #[0,1,1] else #[0,0,1]) else (if j.val < 13 then #[0,1,1] else #[0,0,1]))))

private def stateBasisRows (j : Fin 14) :
    Array (Fin 14) :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then #[0,6,7] else (if j.val < 2 then #[1,7] else #[7])) else (if j.val < 5 then (if j.val < 4 then #[6] else #[4,5,6]) else (if j.val < 6 then #[4,6,7] else #[7,6,7]))) else (if j.val < 10 then (if j.val < 8 then #[6,7,6] else (if j.val < 9 then #[9,6,7] else #[8,9,6])) else (if j.val < 12 then (if j.val < 11 then #[11,6,7] else #[10,11,6]) else (if j.val < 13 then #[13,6,7] else #[12,13,6]))))

private def termGenerator (j : Fin 14)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 14)
    (t : Fin (termCount j)) : Fin 14 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 14)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow5ModuleRepresentation.states 11).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow5ModuleRepresentation.charts 11).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow5ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow5ModuleRepresentation.representation PrimitiveAffineEightFrameRow5TopCertificate.ambient
      (PrimitiveAffineEightFrameRow5ModuleRepresentation.states 11) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D11

namespace D12

private def displacementBasis (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 10 else 17)) else (if j.val < 5 then (if j.val < 4 then 34 else 65) else (if j.val < 6 then 130 else 259))) else (if j.val < 10 then (if j.val < 8 then 514 else (if j.val < 9 then 1027 else 2050)) else (if j.val < 12 then (if j.val < 11 then 4099 else 8194) else (if j.val < 13 then 16387 else 32770))))

private def displacementDual (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 8 else 16)) else (if j.val < 5 then (if j.val < 4 then 32 else 64) else (if j.val < 6 then 128 else 256))) else (if j.val < 10 then (if j.val < 8 then 512 else (if j.val < 9 then 1024 else 2048)) else (if j.val < 12 then (if j.val < 11 then 4096 else 8192) else (if j.val < 13 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 14 :=
  binaryCoordinateSpaceOfMasks 16 14
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow5ModuleRepresentation.states 12).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow5ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow5ModuleRepresentation.charts 12).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 3 else 2)) else (if j.val < 5 then (if j.val < 4 then 1 else 3) else (if j.val < 6 then 2 else 3))) else (if j.val < 10 then (if j.val < 8 then 3 else (if j.val < 9 then 3 else 3)) else (if j.val < 12 then (if j.val < 11 then 3 else 3) else (if j.val < 13 then 3 else 3))))

private def generatorRows (j : Fin 14) :
    Array (Fin 7) :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0,1,1] else #[1,1])) else (if j.val < 5 then (if j.val < 4 then #[1] else #[0,0,1]) else (if j.val < 6 then #[0,1] else #[0,1,1]))) else (if j.val < 10 then (if j.val < 8 then #[0,0,1] else (if j.val < 9 then #[0,1,1] else #[0,0,1])) else (if j.val < 12 then (if j.val < 11 then #[0,1,1] else #[0,0,1]) else (if j.val < 13 then #[0,1,1] else #[0,0,1]))))

private def stateBasisRows (j : Fin 14) :
    Array (Fin 14) :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then #[0,6] else (if j.val < 2 then #[1,6,7] else #[6,7])) else (if j.val < 5 then (if j.val < 4 then #[7] else #[4,5,7]) else (if j.val < 6 then #[4,6] else #[7,6,7]))) else (if j.val < 10 then (if j.val < 8 then #[6,7,6] else (if j.val < 9 then #[9,6,7] else #[8,9,6])) else (if j.val < 12 then (if j.val < 11 then #[11,6,7] else #[10,11,6]) else (if j.val < 13 then #[13,6,7] else #[12,13,6]))))

private def termGenerator (j : Fin 14)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 14)
    (t : Fin (termCount j)) : Fin 14 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 14)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow5ModuleRepresentation.states 12).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow5ModuleRepresentation.charts 12).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow5ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow5ModuleRepresentation.representation PrimitiveAffineEightFrameRow5TopCertificate.ambient
      (PrimitiveAffineEightFrameRow5ModuleRepresentation.states 12) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D12

namespace D13

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
      (PrimitiveAffineEightFrameRow5ModuleRepresentation.states 13).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow5ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow5ModuleRepresentation.charts 13).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 16) : ℕ :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 3 else 4)) else (if j.val < 6 then (if j.val < 5 then 4 else 2) else (if j.val < 7 then 2 else 1))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 1 else 2) else (if j.val < 11 then 1 else 2)) else (if j.val < 14 then (if j.val < 13 then 1 else 2) else (if j.val < 15 then 1 else 2))))

private def generatorRows (j : Fin 16) :
    Array (Fin 7) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,1] else #[0,1,1]) else (if j.val < 3 then #[0,0,1] else #[0,0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,0,1,1] else #[0,1]) else (if j.val < 7 then #[0,0] else #[0]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[0] else #[0,0]) else (if j.val < 11 then #[0] else #[0,0])) else (if j.val < 14 then (if j.val < 13 then #[0] else #[0,0]) else (if j.val < 15 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 16) :
    Array (Fin 16) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1] else #[0,0,1]) else (if j.val < 3 then #[1,2,0] else #[0,1,3,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1,0,1] else #[0,0]) else (if j.val < 7 then #[6,7] else #[6]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[9] else #[8,9]) else (if j.val < 11 then #[11] else #[10,11])) else (if j.val < 14 then (if j.val < 13 then #[13] else #[12,13]) else (if j.val < 15 then #[15] else #[14,15]))))

private def termGenerator (j : Fin 16)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 16)
    (t : Fin (termCount j)) : Fin 16 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 16)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow5ModuleRepresentation.states 13).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow5ModuleRepresentation.charts 13).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow5ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow5ModuleRepresentation.representation PrimitiveAffineEightFrameRow5TopCertificate.ambient
      (PrimitiveAffineEightFrameRow5ModuleRepresentation.states 13) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D13

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRegistry

end
