import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 16–23. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistry

local instance sourceGroupDisplacement16 : Group Source := PrimitiveAffineEightFrameRow9TopCertificate.group
local instance sourceInhabitedDisplacement16 : Inhabited Source := ⟨1⟩

namespace D16

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 3855)) else (if j.val < 5 then (if j.val < 4 then 5140 else 8738) else (if j.val < 6 then 16660 else 34605)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 2048)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 16).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 16).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 1)) else (if j.val < 5 then (if j.val < 4 then 2 else 2) else (if j.val < 6 then 3 else 3)))

private def generatorRows (j : Fin 7) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[1] else #[0])) else (if j.val < 5 then (if j.val < 4 then #[0,1] else #[0,1]) else (if j.val < 6 then #[0,0,1] else #[0,0,1])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 9) :=
  (if j.val < 3 then (if j.val < 1 then #[1,1] else (if j.val < 2 then #[1] else #[3])) else (if j.val < 5 then (if j.val < 4 then #[3,4] else #[5,4]) else (if j.val < 6 then #[5,7,7] else #[3,5,7])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 16).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 16).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation PrimitiveAffineEightFrameRow9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 16) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D16

namespace D17

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
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 17).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 17).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 1 else 3) else (if j.val < 7 then 2 else (if j.val < 8 then 4 else 2))))

private def generatorRows (j : Fin 9) :
    Array (Fin 7) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[1]) else (if j.val < 3 then #[0,0,1] else #[0,1])) else (if j.val < 6 then (if j.val < 5 then #[6] else #[0,1,6]) else (if j.val < 7 then #[1,6] else (if j.val < 8 then #[0,0,1,6] else #[0,1]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,0] else #[0]) else (if j.val < 3 then #[1,3,3] else #[1,3])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[6,5,0]) else (if j.val < 7 then #[5,0] else (if j.val < 8 then #[6,8,8,0] else #[6,8]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 17).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 17).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation PrimitiveAffineEightFrameRow9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 17) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D17

namespace D18

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
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 18).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 18).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 1 else 3) else (if j.val < 7 then 3 else (if j.val < 8 then 5 else 5))))

private def generatorRows (j : Fin 9) :
    Array (Fin 7) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[0,1,1] else #[1,1])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[0,1,1]) else (if j.val < 7 then #[0,1,1] else (if j.val < 8 then #[0,0,0,1,1] else #[0,0,0,1,1]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[2,1,2] else #[1,2])) else (if j.val < 6 then (if j.val < 5 then #[4] else #[4,1,5]) else (if j.val < 7 then #[6,1,5] else (if j.val < 8 then #[0,6,8,1,8] else #[0,4,6,1,8]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 18).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 18).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation PrimitiveAffineEightFrameRow9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 18) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D18

namespace D19

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
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 19).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 19).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 1 else 3) else (if j.val < 7 then 3 else (if j.val < 8 then 5 else 5))))

private def generatorRows (j : Fin 9) :
    Array (Fin 7) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[0,1,1] else #[1,1])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[0,0,1]) else (if j.val < 7 then #[0,0,1] else (if j.val < 8 then #[0,0,0,1,1] else #[0,0,0,1,1]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[2,1,2] else #[1,2])) else (if j.val < 6 then (if j.val < 5 then #[4] else #[0,4,5]) else (if j.val < 7 then #[0,6,5] else (if j.val < 8 then #[0,6,8,1,8] else #[0,4,6,1,8]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 19).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 19).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation PrimitiveAffineEightFrameRow9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 19) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D19

namespace D20

private def displacementBasis (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 57 else 85) else (if j.val < 3 then 147 else 1285)) else (if j.val < 6 then (if j.val < 5 then 2570 else 4369) else (if j.val < 7 then 8731 else (if j.val < 8 then 16660 else 33297))))

private def displacementDual (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 32 else 64) else (if j.val < 3 then 128 else 1024)) else (if j.val < 6 then (if j.val < 5 then 2048 else 4096) else (if j.val < 7 then 8192 else (if j.val < 8 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 9 :=
  binaryCoordinateSpaceOfMasks 16 9
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 20).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 20).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 3) else (if j.val < 3 then 2 else 2)) else (if j.val < 6 then (if j.val < 5 then 3 else 2) else (if j.val < 7 then 2 else (if j.val < 8 then 3 else 5))))

private def generatorRows (j : Fin 9) :
    Array (Fin 7) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0,1]) else (if j.val < 3 then #[0,1] else #[1,6])) else (if j.val < 6 then (if j.val < 5 then #[0,1,6] else #[0,6]) else (if j.val < 7 then #[0,1] else (if j.val < 8 then #[0,0,1] else #[0,0,1,1,6]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,2,2]) else (if j.val < 3 then #[0,2] else #[5,0])) else (if j.val < 6 then (if j.val < 5 then #[4,5,0] else #[4,0]) else (if j.val < 7 then #[6,5] else (if j.val < 8 then #[6,8,8] else #[4,6,5,8,0]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 20).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 20).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation PrimitiveAffineEightFrameRow9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 20) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D20

namespace D21

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
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 21).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 21).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 1 else 3) else (if j.val < 7 then 3 else (if j.val < 8 then 3 else 3))))

private def generatorRows (j : Fin 9) :
    Array (Fin 7) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[1]) else (if j.val < 3 then #[0,0,1] else #[0,1])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[0,0,1]) else (if j.val < 7 then #[0,0,1] else (if j.val < 8 then #[0,0,1] else #[0,0,1]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 11) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,0] else #[0]) else (if j.val < 3 then #[1,3,3] else #[1,3])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[1,5,6]) else (if j.val < 7 then #[1,7,6] else (if j.val < 8 then #[7,9,9] else #[5,7,9]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 21).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 21).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation PrimitiveAffineEightFrameRow9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 21) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D21

namespace D22

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
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 22).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 22).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 2 else (if j.val < 4 then 3 else 3))) else (if j.val < 8 then (if j.val < 6 then 1 else (if j.val < 7 then 2 else 3)) else (if j.val < 9 then 2 else (if j.val < 10 then 3 else 4))))

private def generatorRows (j : Fin 11) :
    Array (Fin 7) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,1]) else (if j.val < 3 then #[0,1] else (if j.val < 4 then #[0,0,1] else #[0,0,1]))) else (if j.val < 8 then (if j.val < 6 then #[6] else (if j.val < 7 then #[0,6] else #[0,1,6])) else (if j.val < 9 then #[0,1] else (if j.val < 10 then #[0,0,1] else #[0,0,1,6]))))

private def stateBasisRows (j : Fin 11) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,1]) else (if j.val < 3 then #[2,1] else (if j.val < 4 then #[2,4,4] else #[0,2,4]))) else (if j.val < 8 then (if j.val < 6 then #[0] else (if j.val < 7 then #[6,0] else #[6,7,0])) else (if j.val < 9 then #[8,7] else (if j.val < 10 then #[8,10,10] else #[6,8,10,0]))))

private def termGenerator (j : Fin 11)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 11)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 11)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 22).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 22).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation PrimitiveAffineEightFrameRow9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 22) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D22

namespace D23

private def displacementBasis (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 10 else 17)) else (if j.val < 5 then (if j.val < 4 then 34 else 65) else (if j.val < 6 then 130 else 257))) else (if j.val < 10 then (if j.val < 8 then 514 else (if j.val < 9 then 1025 else 2050)) else (if j.val < 12 then (if j.val < 11 then 4097 else 8194) else (if j.val < 13 then 16385 else 32770))))

private def displacementDual (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 8 else 16)) else (if j.val < 5 then (if j.val < 4 then 32 else 64) else (if j.val < 6 then 128 else 256))) else (if j.val < 10 then (if j.val < 8 then 512 else (if j.val < 9 then 1024 else 2048)) else (if j.val < 12 then (if j.val < 11 then 4096 else 8192) else (if j.val < 13 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 14 :=
  binaryCoordinateSpaceOfMasks 16 14
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 23).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 23).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 3 else (if j.val < 2 then 2 else 1)) else (if j.val < 5 then (if j.val < 4 then 2 else 3) else (if j.val < 6 then 4 else 3))) else (if j.val < 10 then (if j.val < 8 then 6 else (if j.val < 9 then 8 else 6)) else (if j.val < 12 then (if j.val < 11 then 4 else 5) else (if j.val < 13 then 3 else 4))))

private def generatorRows (j : Fin 14) :
    Array (Fin 7) :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then #[0,1,2] else (if j.val < 2 then #[1,2] else #[2])) else (if j.val < 5 then (if j.val < 4 then #[0,1] else #[0,0,1]) else (if j.val < 6 then #[0,1,1,2] else #[0,0,1]))) else (if j.val < 10 then (if j.val < 8 then #[0,0,1,1,2,4] else (if j.val < 9 then #[0,0,0,0,1,1,1,4] else #[0,0,0,1,1,2])) else (if j.val < 12 then (if j.val < 11 then #[0,0,1,4] else #[0,1,1,2,4]) else (if j.val < 13 then #[0,0,1] else #[0,1,1,2]))))

private def stateBasisRows (j : Fin 14) :
    Array (Fin 14) :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then #[0,1,6] else (if j.val < 2 then #[1,6] else #[6])) else (if j.val < 5 then (if j.val < 4 then #[2,1] else #[2,4,4]) else (if j.val < 6 then #[2,1,4,6] else #[2,10,6]))) else (if j.val < 10 then (if j.val < 8 then #[2,10,6,7,6,6] else (if j.val < 9 then #[0,2,7,10,1,6,7,6] else #[2,6,10,1,6,6])) else (if j.val < 12 then (if j.val < 11 then #[2,10,6,6] else #[2,1,6,6,6]) else (if j.val < 13 then #[2,12,12] else #[2,1,12,6]))))

private def termGenerator (j : Fin 14)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 14)
    (t : Fin (termCount j)) : Fin 14 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 14)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 23).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 23).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation PrimitiveAffineEightFrameRow9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 23) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D23

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistry

end
