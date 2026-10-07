import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 32–39. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleRegistry

local instance sourceGroupDisplacement32 : Group Source := PrimitiveAffineEightFrameRow8TopCertificate.group
local instance sourceInhabitedDisplacement32 : Inhabited Source := ⟨1⟩

namespace D32

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 300 else (if j.val < 4 then 537 else 1065))) else (if j.val < 7 then (if j.val < 6 then 2067 else 4157) else (if j.val < 8 then 8251 else (if j.val < 9 then 16440 else 32817))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 32).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 32).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 2 else (if j.val < 4 then 5 else 6))) else (if j.val < 7 then (if j.val < 6 then 3 else 4) else (if j.val < 8 then 3 else (if j.val < 9 then 2 else 1))))

private def generatorRows (j : Fin 10) :
    Array (Fin 5) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[1]) else (if j.val < 3 then #[0,1] else (if j.val < 4 then #[0,0,1,1,2] else #[0,0,0,1,1,2]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,1] else #[0,0,1,2]) else (if j.val < 8 then #[0,1,2] else (if j.val < 9 then #[0,1] else #[1]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[6,2] else (if j.val < 4 then #[0,6,2,3,2] else #[0,3,6,2,3,2]))) else (if j.val < 7 then (if j.val < 6 then #[2,6,2] else #[0,6,2,2]) else (if j.val < 8 then #[0,2,2] else (if j.val < 9 then #[8,8] else #[8]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 32).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 32).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow8ModuleRepresentation.representation PrimitiveAffineEightFrameRow8TopCertificate.ambient
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 32) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D32

namespace D33

private def displacementBasis (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 27 else 45) else (if j.val < 3 then 78 else 135)) else (if j.val < 6 then (if j.val < 5 then 3855 else 5135) else (if j.val < 7 then 8719 else (if j.val < 8 then 16655 else 34560))))

private def displacementDual (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else 128)) else (if j.val < 6 then (if j.val < 5 then 2048 else 4096) else (if j.val < 7 then 8192 else (if j.val < 8 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 9 :=
  binaryCoordinateSpaceOfMasks 16 9
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 33).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 33).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 1 else 3) else (if j.val < 7 then 3 else (if j.val < 8 then 3 else 3))))

private def generatorRows (j : Fin 9) :
    Array (Fin 5) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[1]) else (if j.val < 3 then #[0,0,1] else #[0,1])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[0,0,1]) else (if j.val < 7 then #[0,0,1] else (if j.val < 8 then #[0,0,1] else #[0,0,1]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 11) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,0] else #[0]) else (if j.val < 3 then #[1,3,3] else #[1,3])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[1,5,6]) else (if j.val < 7 then #[1,7,6] else (if j.val < 8 then #[7,9,9] else #[5,7,9]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 33).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 33).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow8ModuleRepresentation.representation PrimitiveAffineEightFrameRow8TopCertificate.ambient
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 33) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D33

namespace D34

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 257 else (if j.val < 4 then 514 else 1028))) else (if j.val < 7 then (if j.val < 6 then 2056 else 4112) else (if j.val < 8 then 8224 else (if j.val < 9 then 16405 else 32810))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 34).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 34).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 2 else (if j.val < 4 then 4 else 5))) else (if j.val < 7 then (if j.val < 6 then 3 else 3) else (if j.val < 8 then 2 else (if j.val < 9 then 2 else 1))))

private def generatorRows (j : Fin 10) :
    Array (Fin 5) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[1]) else (if j.val < 3 then #[0,1] else (if j.val < 4 then #[0,1,1,2] else #[0,0,1,1,2]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,1] else #[0,1,2]) else (if j.val < 8 then #[1,2] else (if j.val < 9 then #[0,1] else #[1]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1,1] else #[1]) else (if j.val < 3 then #[7,3] else (if j.val < 4 then #[7,3,4,3] else #[4,7,3,4,3]))) else (if j.val < 7 then (if j.val < 6 then #[3,7,3] else #[7,3,3]) else (if j.val < 8 then #[3,3] else (if j.val < 9 then #[9,9] else #[9]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 34).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 34).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow8ModuleRepresentation.representation PrimitiveAffineEightFrameRow8TopCertificate.ambient
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 34) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D34

namespace D35

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 300 else (if j.val < 4 then 537 else 1065))) else (if j.val < 7 then (if j.val < 6 then 2067 else 4157) else (if j.val < 8 then 8251 else (if j.val < 9 then 16440 else 32817))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 35).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 35).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 2 else (if j.val < 4 then 6 else 7))) else (if j.val < 7 then (if j.val < 6 then 3 else 5) else (if j.val < 8 then 4 else (if j.val < 9 then 2 else 1))))

private def generatorRows (j : Fin 10) :
    Array (Fin 5) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[1]) else (if j.val < 3 then #[0,1] else (if j.val < 4 then #[0,0,1,1,1,2] else #[0,0,0,1,1,1,2]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,1] else #[0,0,1,1,2]) else (if j.val < 8 then #[0,1,1,2] else (if j.val < 9 then #[0,1] else #[1]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1,1] else #[1]) else (if j.val < 3 then #[7,3] else (if j.val < 4 then #[1,7,1,3,4,3] else #[1,4,7,1,3,4,3]))) else (if j.val < 7 then (if j.val < 6 then #[3,7,3] else #[1,7,1,3,3]) else (if j.val < 8 then #[1,1,3,3] else (if j.val < 9 then #[9,9] else #[9]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 35).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 35).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow8ModuleRepresentation.representation PrimitiveAffineEightFrameRow8TopCertificate.ambient
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 35) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D35

namespace D36

private def displacementBasis (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 15 else 20) else (if j.val < 3 then 34 else (if j.val < 4 then 65 else 135))) else (if j.val < 8 then (if j.val < 6 then 1285 else (if j.val < 7 then 2565 else 4357)) else (if j.val < 9 then 8704 else (if j.val < 10 then 16640 else 33285))))

private def displacementDual (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 8 else 16) else (if j.val < 3 then 32 else (if j.val < 4 then 64 else 128))) else (if j.val < 8 then (if j.val < 6 then 1024 else (if j.val < 7 then 2048 else 4096)) else (if j.val < 9 then 8192 else (if j.val < 10 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 11 :=
  binaryCoordinateSpaceOfMasks 16 11
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 36).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 36).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 2 else (if j.val < 4 then 3 else 3))) else (if j.val < 8 then (if j.val < 6 then 1 else (if j.val < 7 then 2 else 3)) else (if j.val < 9 then 2 else (if j.val < 10 then 3 else 4))))

private def generatorRows (j : Fin 11) :
    Array (Fin 5) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,1]) else (if j.val < 3 then #[0,1] else (if j.val < 4 then #[0,0,1] else #[0,0,1]))) else (if j.val < 8 then (if j.val < 6 then #[4] else (if j.val < 7 then #[0,4] else #[0,1,4])) else (if j.val < 9 then #[0,1] else (if j.val < 10 then #[0,0,1] else #[0,0,1,4]))))

private def stateBasisRows (j : Fin 11) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,1]) else (if j.val < 3 then #[2,1] else (if j.val < 4 then #[2,4,4] else #[0,2,4]))) else (if j.val < 8 then (if j.val < 6 then #[0] else (if j.val < 7 then #[6,0] else #[6,7,0])) else (if j.val < 9 then #[8,7] else (if j.val < 10 then #[8,10,10] else #[6,8,10,0]))))

private def termGenerator (j : Fin 11)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 11)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 11)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 36).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 36).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow8ModuleRepresentation.representation PrimitiveAffineEightFrameRow8TopCertificate.ambient
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 36) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D36

namespace D37

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 27 else (if j.val < 2 then 45 else 78)) else (if j.val < 4 then 135 else (if j.val < 5 then 257 else 514))) else (if j.val < 9 then (if j.val < 7 then 1028 else (if j.val < 8 then 2056 else 4107)) else (if j.val < 10 then 8205 else (if j.val < 11 then 16398 else 32775))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 16 else (if j.val < 2 then 32 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 37).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 37).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 3)) else (if j.val < 4 then 2 else (if j.val < 5 then 3 else 5))) else (if j.val < 9 then (if j.val < 7 then 6 else (if j.val < 8 then 4 else 5)) else (if j.val < 10 then 4 else (if j.val < 11 then 3 else 2))))

private def generatorRows (j : Fin 12) :
    Array (Fin 5) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[1] else (if j.val < 2 then #[0,1] else #[0,1,1])) else (if j.val < 4 then #[1,1] else (if j.val < 5 then #[0,0,1] else #[0,0,1,1,2]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,0,1,1,2] else (if j.val < 8 then #[0,0,0,1] else #[0,0,1,1,2])) else (if j.val < 10 then #[0,1,1,2] else (if j.val < 11 then #[0,1,1] else #[1,1]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 12) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[1] else (if j.val < 2 then #[0,1] else #[2,1,2])) else (if j.val < 4 then #[1,2] else (if j.val < 5 then #[0,8,4] else #[0,8,4,5,4]))) else (if j.val < 9 then (if j.val < 7 then #[0,5,8,4,5,4] else (if j.val < 8 then #[0,4,8,4] else #[0,8,1,4,4])) else (if j.val < 10 then #[0,1,4,4] else (if j.val < 11 then #[10,1,10] else #[1,10]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 37).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 37).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow8ModuleRepresentation.representation PrimitiveAffineEightFrameRow8TopCertificate.ambient
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 37) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D37

namespace D38

private def displacementBasis (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 57 else 85) else (if j.val < 3 then 147 else (if j.val < 4 then 257 else 514))) else (if j.val < 8 then (if j.val < 6 then 1028 else (if j.val < 7 then 2056 else 4112)) else (if j.val < 9 then 8217 else (if j.val < 10 then 16405 else 32787))))

private def displacementDual (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 32 else 64) else (if j.val < 3 then 128 else (if j.val < 4 then 256 else 512))) else (if j.val < 8 then (if j.val < 6 then 1024 else (if j.val < 7 then 2048 else 4096)) else (if j.val < 9 then 8192 else (if j.val < 10 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 11 :=
  binaryCoordinateSpaceOfMasks 16 11
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 38).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 38).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 3) else (if j.val < 3 then 2 else (if j.val < 4 then 3 else 5))) else (if j.val < 8 then (if j.val < 6 then 6 else (if j.val < 7 then 4 else 4)) else (if j.val < 9 then 3 else (if j.val < 10 then 3 else 2))))

private def generatorRows (j : Fin 11) :
    Array (Fin 5) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0,1]) else (if j.val < 3 then #[0,1] else (if j.val < 4 then #[0,0,1] else #[0,0,1,1,2]))) else (if j.val < 8 then (if j.val < 6 then #[0,0,0,1,1,2] else (if j.val < 7 then #[0,0,0,1] else #[0,0,1,2])) else (if j.val < 9 then #[0,1,2] else (if j.val < 10 then #[0,0,1] else #[0,1]))))

private def stateBasisRows (j : Fin 11) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,2,2]) else (if j.val < 3 then #[0,2] else (if j.val < 4 then #[0,8,4] else #[0,8,4,5,4]))) else (if j.val < 8 then (if j.val < 6 then #[0,5,8,4,5,4] else (if j.val < 7 then #[0,4,8,4] else #[0,8,4,4])) else (if j.val < 9 then #[0,4,4] else (if j.val < 10 then #[0,10,10] else #[0,10]))))

private def termGenerator (j : Fin 11)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 11)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 11)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 38).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 38).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow8ModuleRepresentation.representation PrimitiveAffineEightFrameRow8TopCertificate.ambient
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 38) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D38

namespace D39

private def displacementBasis (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 57 else 85) else (if j.val < 3 then 147 else (if j.val < 4 then 277 else 537))) else (if j.val < 8 then (if j.val < 6 then 1040 else (if j.val < 7 then 2067 else 4100)) else (if j.val < 9 then 8194 else (if j.val < 10 then 16385 else 32776))))

private def displacementDual (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 32 else 64) else (if j.val < 3 then 128 else (if j.val < 4 then 256 else 512))) else (if j.val < 8 then (if j.val < 6 then 1024 else (if j.val < 7 then 2048 else 4096)) else (if j.val < 9 then 8192 else (if j.val < 10 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 11 :=
  binaryCoordinateSpaceOfMasks 16 11
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 39).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 39).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 3) else (if j.val < 3 then 2 else (if j.val < 4 then 3 else 5))) else (if j.val < 8 then (if j.val < 6 then 6 else (if j.val < 7 then 4 else 5)) else (if j.val < 9 then 4 else (if j.val < 10 then 3 else 2))))

private def generatorRows (j : Fin 11) :
    Array (Fin 5) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0,1]) else (if j.val < 3 then #[0,1] else (if j.val < 4 then #[0,0,1] else #[0,1,1,1,2]))) else (if j.val < 8 then (if j.val < 6 then #[0,0,1,1,1,2] else (if j.val < 7 then #[0,0,0,1] else #[0,0,1,1,2])) else (if j.val < 9 then #[0,1,1,2] else (if j.val < 10 then #[0,0,1] else #[0,1]))))

private def stateBasisRows (j : Fin 11) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,2,2]) else (if j.val < 3 then #[0,2] else (if j.val < 4 then #[0,8,4] else #[8,2,4,5,4]))) else (if j.val < 8 then (if j.val < 6 then #[5,8,2,4,5,4] else (if j.val < 7 then #[0,4,8,4] else #[0,8,2,4,4])) else (if j.val < 9 then #[0,2,4,4] else (if j.val < 10 then #[0,10,10] else #[0,10]))))

private def termGenerator (j : Fin 11)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 11)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 11)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 39).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 39).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow8ModuleRepresentation.representation PrimitiveAffineEightFrameRow8TopCertificate.ambient
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 39) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D39

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleRegistry

end
