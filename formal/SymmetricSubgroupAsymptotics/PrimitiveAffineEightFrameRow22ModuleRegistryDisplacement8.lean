import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 8–15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistry

local instance sourceGroupDisplacement8 : Group Source := PrimitiveAffineEightFrameTop13TopCertificate.group
local instance sourceInhabitedDisplacement8 : Inhabited Source := ⟨1⟩

namespace D8

private def displacementBasis (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1530 else 2655) else (if j.val < 3 then 20655 else 41205))

private def displacementDual (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1024 else 2048) else (if j.val < 3 then 16384 else 32768))

def displacementChart :
    BinaryCoordinateSpace 16 4 :=
  binaryCoordinateSpaceOfMasks 16 4
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 8).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 8).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 3 else 2) else (if j.val < 3 then 1 else 2))

private def generatorRows (j : Fin 4) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[4,4,4] else #[4,4]) else (if j.val < 3 then #[4] else #[4,4]))

private def stateBasisRows (j : Fin 4) :
    Array (Fin 5) :=
  (if j.val < 2 then (if j.val < 1 then #[0,2,3] else #[1,2]) else (if j.val < 3 then #[3] else #[0,3]))

private def termGenerator (j : Fin 4)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 4)
    (t : Fin (termCount j)) : Fin 5 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 4)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 8).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 8).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow22ModuleRepresentation.representation PrimitiveAffineEightFrameTop13TopCertificate.ambient
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 8) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D8

namespace D9

private def displacementBasis (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1530 else 2655) else (if j.val < 3 then 20655 else 41205))

private def displacementDual (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1024 else 2048) else (if j.val < 3 then 16384 else 32768))

def displacementChart :
    BinaryCoordinateSpace 16 4 :=
  binaryCoordinateSpaceOfMasks 16 4
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 9).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 9).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 3 else 4) else (if j.val < 3 then 1 else 2))

private def generatorRows (j : Fin 4) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[4,4,4] else #[4,4,4,4]) else (if j.val < 3 then #[4] else #[4,4]))

private def stateBasisRows (j : Fin 4) :
    Array (Fin 5) :=
  (if j.val < 2 then (if j.val < 1 then #[0,2,3] else #[0,1,2,3]) else (if j.val < 3 then #[0] else #[0,3]))

private def termGenerator (j : Fin 4)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 4)
    (t : Fin (termCount j)) : Fin 5 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 4)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 9).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 9).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow22ModuleRepresentation.representation PrimitiveAffineEightFrameTop13TopCertificate.ambient
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 9) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D9

namespace D10

private def displacementBasis (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1530 else 2655) else (if j.val < 3 then 20655 else 41205))

private def displacementDual (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1024 else 2048) else (if j.val < 3 then 16384 else 32768))

def displacementChart :
    BinaryCoordinateSpace 16 4 :=
  binaryCoordinateSpaceOfMasks 16 4
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 10).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 10).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 2 else 1))

private def generatorRows (j : Fin 4) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[4] else #[4,4]) else (if j.val < 3 then #[4,4] else #[4]))

private def stateBasisRows (j : Fin 4) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[3] else #[2,3]) else (if j.val < 3 then #[0,1] else #[0]))

private def termGenerator (j : Fin 4)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 4)
    (t : Fin (termCount j)) : Fin 6 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 4)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 10).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 10).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow22ModuleRepresentation.representation PrimitiveAffineEightFrameTop13TopCertificate.ambient
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 10) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D10

namespace D11

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 5 else 10) else (if j.val < 3 then 80 else 160)) else (if j.val < 6 then (if j.val < 5 then 1280 else 2560) else (if j.val < 7 then 20480 else 40960)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 4 else 8) else (if j.val < 3 then 64 else 128)) else (if j.val < 6 then (if j.val < 5 then 1024 else 2048) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 11).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 11).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 4 else 4) else (if j.val < 3 then 4 else 3)) else (if j.val < 6 then (if j.val < 5 then 1 else 2) else (if j.val < 7 then 5 else 3)))

private def generatorRows (j : Fin 8) :
    Array (Fin 6) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[4,4,4,5] else #[4,4,5,5]) else (if j.val < 3 then #[4,4,4,5] else #[4,4,5])) else (if j.val < 6 then (if j.val < 5 then #[4] else #[4,4]) else (if j.val < 7 then #[4,4,4,5,5] else #[4,4,5])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,2,1] else #[0,3,0,1]) else (if j.val < 3 then #[0,2,3,0] else #[1,2,1])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[4,5]) else (if j.val < 7 then #[0,1,2,0,1] else #[0,3,0])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 11).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 11).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow22ModuleRepresentation.representation PrimitiveAffineEightFrameTop13TopCertificate.ambient
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 11) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D11

namespace D12

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 5 else 10) else (if j.val < 3 then 80 else (if j.val < 4 then 160 else 1280))) else (if j.val < 7 then (if j.val < 6 then 2560 else 4369) else (if j.val < 8 then 8738 else (if j.val < 9 then 16657 else 33314))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 4 else 8) else (if j.val < 3 then 64 else (if j.val < 4 then 128 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 12).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 12).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 1) else (if j.val < 3 then 1 else (if j.val < 4 then 1 else 1))) else (if j.val < 7 then (if j.val < 6 then 1 else 1) else (if j.val < 8 then 2 else (if j.val < 9 then 2 else 3))))

private def generatorRows (j : Fin 10) :
    Array (Fin 6) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1] else #[1]) else (if j.val < 3 then #[2] else (if j.val < 4 then #[2] else #[3]))) else (if j.val < 7 then (if j.val < 6 then #[3] else #[4]) else (if j.val < 8 then #[4,4] else (if j.val < 9 then #[0,4] else #[0,4,4]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[6] else #[7]) else (if j.val < 3 then #[6] else (if j.val < 4 then #[7] else #[6]))) else (if j.val < 7 then (if j.val < 6 then #[7] else #[7]) else (if j.val < 8 then #[6,7] else (if j.val < 9 then #[6,7] else #[7,6,7]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 12).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 12).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow22ModuleRepresentation.representation PrimitiveAffineEightFrameTop13TopCertificate.ambient
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 12) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D12

namespace D13

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 5 else 10) else (if j.val < 3 then 80 else (if j.val < 4 then 160 else 1280))) else (if j.val < 7 then (if j.val < 6 then 2560 else 4369) else (if j.val < 8 then 8738 else (if j.val < 9 then 16657 else 33314))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 4 else 8) else (if j.val < 3 then 64 else (if j.val < 4 then 128 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 13).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 13).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 2 else (if j.val < 4 then 1 else 1))) else (if j.val < 7 then (if j.val < 6 then 1 else 1) else (if j.val < 8 then 2 else (if j.val < 9 then 2 else 3))))

private def generatorRows (j : Fin 10) :
    Array (Fin 6) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1,1] else #[1]) else (if j.val < 3 then #[2,2] else (if j.val < 4 then #[2] else #[3]))) else (if j.val < 7 then (if j.val < 6 then #[3] else #[4]) else (if j.val < 8 then #[4,4] else (if j.val < 9 then #[0,4] else #[0,4,4]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[4,7] else #[7]) else (if j.val < 3 then #[4,7] else (if j.val < 4 then #[4] else #[4]))) else (if j.val < 7 then (if j.val < 6 then #[8] else #[8]) else (if j.val < 8 then #[4,8] else (if j.val < 9 then #[7,8] else #[8,4,8]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 13).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 13).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow22ModuleRepresentation.representation PrimitiveAffineEightFrameTop13TopCertificate.ambient
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 13) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D13

namespace D14

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 5 else 10) else (if j.val < 3 then 80 else (if j.val < 4 then 160 else 1280))) else (if j.val < 7 then (if j.val < 6 then 2560 else 4369) else (if j.val < 8 then 8738 else (if j.val < 9 then 16657 else 33314))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 4 else 8) else (if j.val < 3 then 64 else (if j.val < 4 then 128 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 14).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 14).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 1 else (if j.val < 4 then 2 else 1))) else (if j.val < 7 then (if j.val < 6 then 1 else 1) else (if j.val < 8 then 2 else (if j.val < 9 then 2 else 3))))

private def generatorRows (j : Fin 10) :
    Array (Fin 6) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1] else #[1,1]) else (if j.val < 3 then #[2] else (if j.val < 4 then #[2,2] else #[3]))) else (if j.val < 7 then (if j.val < 6 then #[3] else #[4]) else (if j.val < 8 then #[4,4] else (if j.val < 9 then #[0,4] else #[0,4,4]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[4] else #[4,8]) else (if j.val < 3 then #[7] else (if j.val < 4 then #[4,7] else #[7]))) else (if j.val < 7 then (if j.val < 6 then #[4] else #[4]) else (if j.val < 8 then #[4,7] else (if j.val < 9 then #[7,4] else #[8,4,7]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 14).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 14).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow22ModuleRepresentation.representation PrimitiveAffineEightFrameTop13TopCertificate.ambient
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 14) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D14

namespace D15

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 5 else 10) else (if j.val < 3 then 80 else (if j.val < 4 then 160 else 1280))) else (if j.val < 7 then (if j.val < 6 then 2560 else 4369) else (if j.val < 8 then 8738 else (if j.val < 9 then 16657 else 33314))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 4 else 8) else (if j.val < 3 then 64 else (if j.val < 4 then 128 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 15).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 15).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 1) else (if j.val < 3 then 1 else (if j.val < 4 then 2 else 1))) else (if j.val < 7 then (if j.val < 6 then 2 else 2) else (if j.val < 8 then 1 else (if j.val < 9 then 3 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 6) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1] else #[1]) else (if j.val < 3 then #[2] else (if j.val < 4 then #[2,2] else #[3]))) else (if j.val < 7 then (if j.val < 6 then #[3,3] else #[4,4]) else (if j.val < 8 then #[4] else (if j.val < 9 then #[0,4,4] else #[0,4]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[7] else #[4]) else (if j.val < 3 then #[4] else (if j.val < 4 then #[4,8] else #[7]))) else (if j.val < 7 then (if j.val < 6 then #[4,7] else #[4,7]) else (if j.val < 8 then #[4] else (if j.val < 9 then #[7,4,7] else #[8,4]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 15).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 15).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow22ModuleRepresentation.representation PrimitiveAffineEightFrameTop13TopCertificate.ambient
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 15) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D15

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistry

end
