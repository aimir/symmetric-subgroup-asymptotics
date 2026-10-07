import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 8–15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistry

local instance sourceGroupDisplacement8 : Group Source := PrimitiveAffineEightFrameRow6TopCertificate.group
local instance sourceInhabitedDisplacement8 : Inhabited Source := ⟨1⟩

namespace D8

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 1285 else 2577)) else (if j.val < 6 then (if j.val < 5 then 4362 else 8738) else (if j.val < 7 then 16655 else 33331)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 8).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow6ModuleRepresentation.charts 8).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 1) else (if j.val < 3 then 1 else 2)) else (if j.val < 6 then (if j.val < 5 then 1 else 2) else (if j.val < 7 then 1 else 2)))

private def generatorRows (j : Fin 8) :
    Array (Fin 7) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[1]) else (if j.val < 3 then #[0] else #[0,0])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[0,0]) else (if j.val < 7 then #[0] else #[0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[2] else #[4]) else (if j.val < 3 then #[3] else #[2,3])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[4,5]) else (if j.val < 7 then #[7] else #[6,7])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 8).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow6ModuleRepresentation.charts 8).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow6ModuleRepresentation.representation PrimitiveAffineEightFrameRow6TopCertificate.ambient
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 8) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D8

namespace D9

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 1320 else 2570)) else (if j.val < 6 then (if j.val < 5 then 4412 else 8719) else (if j.val < 7 then 16660 else 33285)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 9).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow6ModuleRepresentation.charts 9).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 1 else 2)) else (if j.val < 6 then (if j.val < 5 then 1 else 2) else (if j.val < 7 then 1 else 2)))

private def generatorRows (j : Fin 8) :
    Array (Fin 7) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,1] else #[1]) else (if j.val < 3 then #[0] else #[0,0])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[0,0]) else (if j.val < 7 then #[0] else #[0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[2,4] else #[2]) else (if j.val < 3 then #[3] else #[2,3])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[4,5]) else (if j.val < 7 then #[7] else #[6,7])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 9).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow6ModuleRepresentation.charts 9).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow6ModuleRepresentation.representation PrimitiveAffineEightFrameRow6TopCertificate.ambient
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 9) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D9

namespace D10

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 1331 else 2620)) else (if j.val < 6 then (if j.val < 5 then 4369 else 8724) else (if j.val < 7 then 16674 else 33320)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 10).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow6ModuleRepresentation.charts 10).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 1 else 2)) else (if j.val < 6 then (if j.val < 5 then 1 else 2) else (if j.val < 7 then 1 else 2)))

private def generatorRows (j : Fin 8) :
    Array (Fin 7) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[1,1]) else (if j.val < 3 then #[0] else #[0,0])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[0,0]) else (if j.val < 7 then #[0] else #[0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[5] else #[3,5]) else (if j.val < 3 then #[3] else #[2,3])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[4,5]) else (if j.val < 7 then #[7] else #[6,7])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 10).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow6ModuleRepresentation.charts 10).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow6ModuleRepresentation.representation PrimitiveAffineEightFrameRow6TopCertificate.ambient
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 10) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D10

namespace D11

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 27 else 45) else (if j.val < 3 then 78 else (if j.val < 4 then 135 else 1285))) else (if j.val < 7 then (if j.val < 6 then 2570 else 4362) else (if j.val < 8 then 8719 else (if j.val < 9 then 16655 else 33285))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else (if j.val < 4 then 128 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 11).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow6ModuleRepresentation.charts 11).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 4 else (if j.val < 4 then 2 else 2))) else (if j.val < 7 then (if j.val < 6 then 3 else 2) else (if j.val < 8 then 4 else (if j.val < 9 then 3 else 3))))

private def generatorRows (j : Fin 10) :
    Array (Fin 7) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0,1,1] else (if j.val < 4 then #[0,1] else #[0,0]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,0] else #[0,0]) else (if j.val < 8 then #[0,0,0,0] else (if j.val < 9 then #[0,0,0] else #[0,0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0]) else (if j.val < 3 then #[0,1,0,1] else (if j.val < 4 then #[0,0] else #[0,5]))) else (if j.val < 7 then (if j.val < 6 then #[1,4,5] else #[1,7]) else (if j.val < 8 then #[0,1,6,7] else (if j.val < 9 then #[0,1,9] else #[0,8,9]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 11).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow6ModuleRepresentation.charts 11).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow6ModuleRepresentation.representation PrimitiveAffineEightFrameRow6TopCertificate.ambient
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 11) displacementChart where
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
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 30 else 39) else (if j.val < 3 then 75 else (if j.val < 4 then 141 else 1285))) else (if j.val < 7 then (if j.val < 6 then 2575 else 4362) else (if j.val < 8 then 8709 else (if j.val < 9 then 16655 else 33290))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else (if j.val < 4 then 128 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 12).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow6ModuleRepresentation.charts 12).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 2 else (if j.val < 4 then 4 else 2))) else (if j.val < 7 then (if j.val < 6 then 4 else 2) else (if j.val < 8 then 3 else (if j.val < 9 then 3 else 3))))

private def generatorRows (j : Fin 10) :
    Array (Fin 7) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,1] else (if j.val < 4 then #[0,0,1,1] else #[0,0]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,0,0] else #[0,0]) else (if j.val < 8 then #[0,0,0] else (if j.val < 9 then #[0,0,0] else #[0,0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[1,1] else (if j.val < 4 then #[0,1,0,1] else #[0,5]))) else (if j.val < 7 then (if j.val < 6 then #[0,1,4,5] else #[1,7]) else (if j.val < 8 then #[0,6,7] else (if j.val < 9 then #[0,1,9] else #[1,8,9]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 12).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow6ModuleRepresentation.charts 12).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow6ModuleRepresentation.representation PrimitiveAffineEightFrameRow6TopCertificate.ambient
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 12) displacementChart where
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
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 30 else 39) else (if j.val < 3 then 75 else (if j.val < 4 then 141 else 1290))) else (if j.val < 7 then (if j.val < 6 then 2565 else 4367) else (if j.val < 8 then 8714 else (if j.val < 9 then 16645 else 33295))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else (if j.val < 4 then 128 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 13).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow6ModuleRepresentation.charts 13).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 2 else (if j.val < 4 then 4 else 2))) else (if j.val < 7 then (if j.val < 6 then 3 else 3) else (if j.val < 8 then 3 else (if j.val < 9 then 2 else 4))))

private def generatorRows (j : Fin 10) :
    Array (Fin 7) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,1] else (if j.val < 4 then #[0,0,1,1] else #[0,0]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,0] else #[0,0,0]) else (if j.val < 8 then #[0,0,0] else (if j.val < 9 then #[0,0] else #[0,0,0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[1,1] else (if j.val < 4 then #[0,1,0,1] else #[1,5]))) else (if j.val < 7 then (if j.val < 6 then #[0,4,5] else #[0,1,7]) else (if j.val < 8 then #[1,6,7] else (if j.val < 9 then #[0,9] else #[0,1,8,9]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 13).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow6ModuleRepresentation.charts 13).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow6ModuleRepresentation.representation PrimitiveAffineEightFrameRow6TopCertificate.ambient
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 13) displacementChart where
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
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 30 else 39) else (if j.val < 3 then 75 else (if j.val < 4 then 141 else 1295))) else (if j.val < 7 then (if j.val < 6 then 2570 else 4357) else (if j.val < 8 then 8719 else (if j.val < 9 then 16650 else 33285))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else (if j.val < 4 then 128 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 14).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow6ModuleRepresentation.charts 14).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 2 else (if j.val < 4 then 4 else 3))) else (if j.val < 7 then (if j.val < 6 then 3 else 2) else (if j.val < 8 then 4 else (if j.val < 9 then 2 else 3))))

private def generatorRows (j : Fin 10) :
    Array (Fin 7) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,1] else (if j.val < 4 then #[0,0,1,1] else #[0,0,0]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,0] else #[0,0]) else (if j.val < 8 then #[0,0,0,0] else (if j.val < 9 then #[0,0] else #[0,0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[1,1] else (if j.val < 4 then #[0,1,0,1] else #[0,1,5]))) else (if j.val < 7 then (if j.val < 6 then #[1,4,5] else #[0,7]) else (if j.val < 8 then #[0,1,6,7] else (if j.val < 9 then #[1,9] else #[0,8,9]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 14).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow6ModuleRepresentation.charts 14).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow6ModuleRepresentation.representation PrimitiveAffineEightFrameRow6TopCertificate.ambient
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 14) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D14

namespace D15

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
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 15).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow6ModuleRepresentation.charts 15).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 1 else 2)) else (if j.val < 4 then 2 else (if j.val < 5 then 2 else 2))) else (if j.val < 9 then (if j.val < 7 then 1 else (if j.val < 8 then 2 else 1)) else (if j.val < 10 then 2 else (if j.val < 11 then 1 else 2))))

private def generatorRows (j : Fin 12) :
    Array (Fin 7) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0] else #[0,0])) else (if j.val < 4 then #[0,0] else (if j.val < 5 then #[0,1] else #[0,1]))) else (if j.val < 9 then (if j.val < 7 then #[0] else (if j.val < 8 then #[0,0] else #[0])) else (if j.val < 10 then #[0,0] else (if j.val < 11 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 12) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[2] else (if j.val < 2 then #[3] else #[0,2])) else (if j.val < 4 then #[1,3] else (if j.val < 5 then #[0,0] else #[1,1]))) else (if j.val < 9 then (if j.val < 7 then #[7] else (if j.val < 8 then #[6,7] else #[9])) else (if j.val < 10 then #[8,9] else (if j.val < 11 then #[11] else #[10,11]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 15).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow6ModuleRepresentation.charts 15).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow6ModuleRepresentation.representation PrimitiveAffineEightFrameRow6TopCertificate.ambient
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states 15) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D15

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistry

end
