import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 16–26. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21ModuleRegistry

local instance sourceGroupDisplacement16 : Group Source := PrimitiveAffineEightFrameRow21TopCertificate.group
local instance sourceInhabitedDisplacement16 : Inhabited Source := ⟨1⟩

namespace D16

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
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 16).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 16).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 2 else (if j.val < 4 then 4 else 3))) else (if j.val < 7 then (if j.val < 6 then 5 else 1) else (if j.val < 8 then 2 else (if j.val < 9 then 5 else 6))))

private def generatorRows (j : Fin 10) :
    Array (Fin 5) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1,1,3] else #[1,3,3]) else (if j.val < 3 then #[1,3] else (if j.val < 4 then #[1,1,3,3] else #[1,2,3]))) else (if j.val < 7 then (if j.val < 6 then #[1,1,2,3,3] else #[3]) else (if j.val < 8 then #[3,3] else (if j.val < 9 then #[0,1,1,3,3] else #[0,1,3,3,3,3]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[6,7,1] else #[6,0,1]) else (if j.val < 3 then #[7,1] else (if j.val < 4 then #[6,7,0,1] else #[7,6,1]))) else (if j.val < 7 then (if j.val < 6 then #[6,7,7,0,1] else #[7]) else (if j.val < 8 then #[6,7] else (if j.val < 9 then #[6,6,7,1,7] else #[7,6,0,1,6,7]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 16).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 16).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow21ModuleRepresentation.representation PrimitiveAffineEightFrameRow21TopCertificate.ambient
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 16) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D16

namespace D17

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
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 17).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 17).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 2 else 3) else (if j.val < 3 then 2 else (if j.val < 4 then 2 else 3))) else (if j.val < 7 then (if j.val < 6 then 3 else 1) else (if j.val < 8 then 2 else (if j.val < 9 then 5 else 6))))

private def generatorRows (j : Fin 10) :
    Array (Fin 5) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1,1] else #[0,1,1]) else (if j.val < 3 then #[1,1] else (if j.val < 4 then #[0,1] else #[0,1,2]))) else (if j.val < 7 then (if j.val < 6 then #[0,1,2] else #[3]) else (if j.val < 8 then #[3,3] else (if j.val < 9 then #[0,0,1,1,3] else #[0,0,1,1,3,3]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[4,8] else #[4,4,8]) else (if j.val < 3 then #[7,8] else (if j.val < 4 then #[4,4] else #[4,4,4]))) else (if j.val < 7 then (if j.val < 6 then #[4,4,8] else #[8]) else (if j.val < 8 then #[4,8] else (if j.val < 9 then #[4,7,4,8,8] else #[4,8,4,8,4,8]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 17).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 17).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow21ModuleRepresentation.representation PrimitiveAffineEightFrameRow21TopCertificate.ambient
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 17) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D17

namespace D18

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
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 18).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 18).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 2 else (if j.val < 4 then 2 else 3))) else (if j.val < 7 then (if j.val < 6 then 3 else 1) else (if j.val < 8 then 2 else (if j.val < 9 then 3 else 6))))

private def generatorRows (j : Fin 10) :
    Array (Fin 5) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[1,1]) else (if j.val < 3 then #[0,1] else (if j.val < 4 then #[1,1] else #[0,1,2]))) else (if j.val < 7 then (if j.val < 6 then #[0,1,2] else #[3]) else (if j.val < 8 then #[3,3] else (if j.val < 9 then #[0,0,3] else #[0,0,1,1,3,3]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[4] else #[7,8]) else (if j.val < 3 then #[4,7] else (if j.val < 4 then #[4,7] else #[4,7,7]))) else (if j.val < 7 then (if j.val < 6 then #[4,4,4] else #[4]) else (if j.val < 8 then #[4,7] else (if j.val < 9 then #[4,7,4] else #[4,8,7,8,4,7]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 18).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 18).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow21ModuleRepresentation.representation PrimitiveAffineEightFrameRow21TopCertificate.ambient
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 18) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D18

namespace D19

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
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 19).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 19).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 3 else 1) else (if j.val < 3 then 2 else (if j.val < 4 then 3 else 3))) else (if j.val < 7 then (if j.val < 6 then 2 else 2) else (if j.val < 8 then 1 else (if j.val < 9 then 6 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 5) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1,1] else #[0]) else (if j.val < 3 then #[0,1] else (if j.val < 4 then #[0,1,1] else #[0,1,2]))) else (if j.val < 7 then (if j.val < 6 then #[2,2] else #[3,3]) else (if j.val < 8 then #[3] else (if j.val < 9 then #[0,0,1,1,3,3] else #[0,3]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[4,4,7] else #[4]) else (if j.val < 3 then #[4,4] else (if j.val < 4 then #[4,4,8] else #[4,4,7]))) else (if j.val < 7 then (if j.val < 6 then #[4,7] else #[4,7]) else (if j.val < 8 then #[4] else (if j.val < 9 then #[4,7,4,7,4,7] else #[8,4]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 19).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 19).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow21ModuleRepresentation.representation PrimitiveAffineEightFrameRow21TopCertificate.ambient
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 19) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D19

namespace D20

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
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 20).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 20).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 4 else (if j.val < 4 then 2 else 3))) else (if j.val < 7 then (if j.val < 6 then 3 else 1) else (if j.val < 8 then 2 else (if j.val < 9 then 4 else 4))))

private def generatorRows (j : Fin 10) :
    Array (Fin 5) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,1,1] else (if j.val < 4 then #[0,1] else #[0,1,2]))) else (if j.val < 7 then (if j.val < 6 then #[0,1,2] else #[3]) else (if j.val < 8 then #[3,3] else (if j.val < 9 then #[0,0,0,3] else #[0,0,3,3]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[5] else #[4,5]) else (if j.val < 3 then #[4,5,4,5] else (if j.val < 4 then #[4,4] else #[4,4,4]))) else (if j.val < 7 then (if j.val < 6 then #[5,5,5] else #[5]) else (if j.val < 8 then #[4,5] else (if j.val < 9 then #[4,5,8,5] else #[4,9,4,5]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 20).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 20).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow21ModuleRepresentation.representation PrimitiveAffineEightFrameRow21TopCertificate.ambient
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 20) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D20

namespace D21

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 10 else 80)) else (if j.val < 4 then 160 else (if j.val < 5 then 306 else 531))) else (if j.val < 9 then (if j.val < 7 then 1074 else (if j.val < 8 then 2067 else 4131)) else (if j.val < 10 then 8241 else (if j.val < 11 then 16419 else 32817))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 8 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 21).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 21).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 2)) else (if j.val < 4 then 4 else (if j.val < 5 then 2 else 3))) else (if j.val < 9 then (if j.val < 7 then 5 else (if j.val < 8 then 6 else 2)) else (if j.val < 10 then 1 else (if j.val < 11 then 4 else 4))))

private def generatorRows (j : Fin 12) :
    Array (Fin 5) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,1])) else (if j.val < 4 then #[0,0,1,1] else (if j.val < 5 then #[3,3] else #[3,3,3]))) else (if j.val < 9 then (if j.val < 7 then #[0,1,2,3,3] else (if j.val < 8 then #[0,1,2,3,3,3] else #[3,3])) else (if j.val < 10 then #[3] else (if j.val < 11 then #[0,0,3,3] else #[0,0,0,3]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 12) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[4,5] else (if j.val < 2 then #[4] else #[5,5])) else (if j.val < 4 then #[4,5,4,5] else (if j.val < 5 then #[5,8] else #[4,5,9]))) else (if j.val < 9 then (if j.val < 7 then #[4,4,4,5,8] else (if j.val < 8 then #[5,5,5,4,5,9] else #[8,9])) else (if j.val < 10 then #[8] else (if j.val < 11 then #[5,8,8,9] else #[4,5,9,8]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 21).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 21).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow21ModuleRepresentation.representation PrimitiveAffineEightFrameRow21TopCertificate.ambient
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 21) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D21

namespace D22

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 10 else 80)) else (if j.val < 4 then 160 else (if j.val < 5 then 306 else 531))) else (if j.val < 9 then (if j.val < 7 then 1074 else (if j.val < 8 then 2067 else 4131)) else (if j.val < 10 then 8241 else (if j.val < 11 then 16419 else 32817))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 8 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 22).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 22).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 2)) else (if j.val < 4 then 2 else (if j.val < 5 then 1 else 4))) else (if j.val < 9 then (if j.val < 7 then 4 else (if j.val < 8 then 5 else 1)) else (if j.val < 10 then 1 else (if j.val < 11 then 3 else 2))))

private def generatorRows (j : Fin 12) :
    Array (Fin 5) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,0] else #[0,1])) else (if j.val < 4 then #[0,1] else (if j.val < 5 then #[3] else #[3,3,3,3]))) else (if j.val < 9 then (if j.val < 7 then #[0,1,2,3] else (if j.val < 8 then #[2,3,3,3,3] else #[3])) else (if j.val < 10 then #[3] else (if j.val < 11 then #[0,0,3] else #[0,3]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 13) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[2] else (if j.val < 2 then #[2,5] else #[2,2])) else (if j.val < 4 then #[5,5] else (if j.val < 5 then #[6] else #[2,5,6,10]))) else (if j.val < 9 then (if j.val < 7 then #[5,5,5,6] else (if j.val < 8 then #[6,2,5,6,10] else #[10])) else (if j.val < 10 then #[2] else (if j.val < 11 then #[5,9,10] else #[10,2]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 13 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 22).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 22).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow21ModuleRepresentation.representation PrimitiveAffineEightFrameRow21TopCertificate.ambient
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 22) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D22

namespace D23

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 10 else 80)) else (if j.val < 4 then 160 else (if j.val < 5 then 306 else 531))) else (if j.val < 9 then (if j.val < 7 then 1074 else (if j.val < 8 then 2067 else 4131)) else (if j.val < 10 then 8241 else (if j.val < 11 then 16419 else 32817))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 8 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 23).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 23).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 1)) else (if j.val < 4 then 2 else (if j.val < 5 then 3 else 2))) else (if j.val < 9 then (if j.val < 7 then 5 else (if j.val < 8 then 4 else 1)) else (if j.val < 10 then 2 else (if j.val < 11 then 4 else 4))))

private def generatorRows (j : Fin 12) :
    Array (Fin 5) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[1])) else (if j.val < 4 then #[0,1] else (if j.val < 5 then #[3,3,3] else #[3,3]))) else (if j.val < 9 then (if j.val < 7 then #[1,2,3,3,3] else (if j.val < 8 then #[1,2,3,3] else #[3])) else (if j.val < 10 then #[3,3] else (if j.val < 11 then #[0,0,0,3] else #[0,0,3,3]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 13) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[2,6] else (if j.val < 2 then #[2] else #[5])) else (if j.val < 4 then #[2,2] else (if j.val < 5 then #[2,6,9] else #[5,6]))) else (if j.val < 9 then (if j.val < 7 then #[5,5,2,6,9] else (if j.val < 8 then #[5,6,5,6] else #[9])) else (if j.val < 10 then #[2,9] else (if j.val < 11 then #[2,6,9,9] else #[6,10,2,9]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 13 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 23).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 23).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow21ModuleRepresentation.representation PrimitiveAffineEightFrameRow21TopCertificate.ambient
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 23) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D23

namespace D24

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 10 else 80)) else (if j.val < 4 then 160 else (if j.val < 5 then 306 else 531))) else (if j.val < 9 then (if j.val < 7 then 1074 else (if j.val < 8 then 2067 else 4131)) else (if j.val < 10 then 8241 else (if j.val < 11 then 16419 else 32817))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 8 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 24).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 24).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 2)) else (if j.val < 4 then 2 else (if j.val < 5 then 3 else 4))) else (if j.val < 9 then (if j.val < 7 then 4 else (if j.val < 8 then 7 else 1)) else (if j.val < 10 then 2 else (if j.val < 11 then 2 else 5))))

private def generatorRows (j : Fin 12) :
    Array (Fin 5) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,0] else #[0,1])) else (if j.val < 4 then #[1,1] else (if j.val < 5 then #[3,3,3] else #[3,3,3,3]))) else (if j.val < 9 then (if j.val < 7 then #[2,3,3,3] else (if j.val < 8 then #[0,1,2,3,3,3,3] else #[3])) else (if j.val < 10 then #[3,3] else (if j.val < 11 then #[0,3] else #[0,0,0,3,3]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 13) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[5] else (if j.val < 2 then #[2,5] else #[2,6])) else (if j.val < 4 then #[2,6] else (if j.val < 5 then #[2,6,9] else #[2,5,6,9]))) else (if j.val < 9 then (if j.val < 7 then #[5,2,6,9] else (if j.val < 8 then #[2,6,6,2,5,6,9] else #[2])) else (if j.val < 10 then #[2,9] else (if j.val < 11 then #[9,2] else #[2,5,10,2,9]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 13 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 24).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 24).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow21ModuleRepresentation.representation PrimitiveAffineEightFrameRow21TopCertificate.ambient
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 24) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D24

namespace D25

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 10 else 80)) else (if j.val < 4 then 160 else (if j.val < 5 then 306 else 531))) else (if j.val < 9 then (if j.val < 7 then 1074 else (if j.val < 8 then 2067 else 4131)) else (if j.val < 10 then 8241 else (if j.val < 11 then 16419 else 32817))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 8 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 25).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 25).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 1 else 2)) else (if j.val < 4 then 2 else (if j.val < 5 then 1 else 2))) else (if j.val < 9 then (if j.val < 7 then 2 else (if j.val < 8 then 3 else 2)) else (if j.val < 10 then 1 else (if j.val < 11 then 4 else 3))))

private def generatorRows (j : Fin 12) :
    Array (Fin 5) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0] else #[0,1])) else (if j.val < 4 then #[0,1] else (if j.val < 5 then #[3] else #[3,3]))) else (if j.val < 9 then (if j.val < 7 then #[2,3] else (if j.val < 8 then #[2,3,3] else #[3,3])) else (if j.val < 10 then #[3] else (if j.val < 11 then #[0,0,3,3] else #[0,0,3]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 14) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[2] else (if j.val < 2 then #[3] else #[2,2])) else (if j.val < 4 then #[3,3] else (if j.val < 5 then #[7] else #[6,7]))) else (if j.val < 9 then (if j.val < 7 then #[6,7] else (if j.val < 8 then #[7,6,7] else #[2,3])) else (if j.val < 10 then #[2] else (if j.val < 11 then #[2,10,2,3] else #[3,11,2]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 14 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 25).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 25).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow21ModuleRepresentation.representation PrimitiveAffineEightFrameRow21TopCertificate.ambient
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 25) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D25

namespace D26

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
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 26).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 26).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 16) : ℕ :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 4 else 4) else (if j.val < 3 then 5 else 5)) else (if j.val < 6 then (if j.val < 5 then 4 else 3) else (if j.val < 7 then 5 else 4))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 1 else 2) else (if j.val < 11 then 2 else 3)) else (if j.val < 14 then (if j.val < 13 then 5 else 3) else (if j.val < 15 then 6 else 4))))

private def generatorRows (j : Fin 16) :
    Array (Fin 5) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[3,3,3,4] else #[3,3,4,4]) else (if j.val < 3 then #[0,3,3,3,4] else #[0,3,3,4,4])) else (if j.val < 6 then (if j.val < 5 then #[3,3,3,4] else #[3,3,4]) else (if j.val < 7 then #[1,3,3,3,4] else #[1,3,3,4]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[3] else #[3,3]) else (if j.val < 11 then #[2,3] else #[2,3,3])) else (if j.val < 14 then (if j.val < 13 then #[3,3,3,4,4] else #[3,3,4]) else (if j.val < 15 then #[0,3,3,3,4,4] else #[0,3,3,4]))))

private def stateBasisRows (j : Fin 16) :
    Array (Fin 16) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,4,1] else #[0,5,0,1]) else (if j.val < 3 then #[0,0,1,4,1] else #[1,0,5,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,4,5,0] else #[1,4,1]) else (if j.val < 7 then #[4,0,4,5,0] else #[5,1,4,1]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[9] else #[8,9]) else (if j.val < 11 then #[8,9] else #[9,8,9])) else (if j.val < 14 then (if j.val < 13 then #[0,1,4,0,1] else #[0,5,0]) else (if j.val < 15 then #[12,0,1,4,0,1] else #[13,0,5,0]))))

private def termGenerator (j : Fin 16)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 16)
    (t : Fin (termCount j)) : Fin 16 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 16)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 26).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow21ModuleRepresentation.charts 26).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow21ModuleRepresentation.representation PrimitiveAffineEightFrameRow21TopCertificate.ambient
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states 26) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D26

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21ModuleRegistry

end
