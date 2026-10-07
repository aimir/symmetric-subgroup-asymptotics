import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 48–55. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

local instance sourceGroupDisplacement48 : Group Source := PrimitiveAffineEightFrameRow0TopCertificate.group
local instance sourceInhabitedDisplacement48 : Inhabited Source := ⟨1⟩

namespace D48

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 3855)) else (if j.val < 5 then (if j.val < 4 then 4369 else 10023) else (if j.val < 6 then 17425 else 33320)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 2048)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 48).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 48).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 2)) else (if j.val < 5 then (if j.val < 4 then 3 else 2) else (if j.val < 6 then 2 else 3)))

private def generatorRows (j : Fin 7) :
    Array (Fin 4) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,0] else #[0,3])) else (if j.val < 5 then (if j.val < 4 then #[0,0,3] else #[0,0]) else (if j.val < 6 then #[0,3] else #[0,0,3])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[2] else (if j.val < 2 then #[1,2] else #[4,0])) else (if j.val < 5 then (if j.val < 4 then #[3,4,0] else #[3,4]) else (if j.val < 6 then #[7,0] else #[6,7,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 48).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 48).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 48) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D48

namespace D49

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 7710)) else (if j.val < 4 then 10023 else (if j.val < 5 then 19230 else 36135)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 49).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 49).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 2)) else (if j.val < 4 then 1 else (if j.val < 5 then 2 else 4)))

private def generatorRows (j : Fin 6) :
    Array (Fin 4) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,0] else #[0,0])) else (if j.val < 4 then #[0] else (if j.val < 5 then #[0,0] else #[0,0,0,0])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[1] else (if j.val < 2 then #[0,1] else #[2,3])) else (if j.val < 4 then #[2] else (if j.val < 5 then #[3,7] else #[2,3,6,7])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 49).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 49).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 49) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D49

namespace D50

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 1285)) else (if j.val < 5 then (if j.val < 4 then 6939 else 8738) else (if j.val < 6 then 19230 else 34850)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 1024)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 50).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 50).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 3)) else (if j.val < 5 then (if j.val < 4 then 1 else 2) else (if j.val < 6 then 2 else 3)))

private def generatorRows (j : Fin 7) :
    Array (Fin 4) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,0] else #[0,0,3])) else (if j.val < 5 then (if j.val < 4 then #[3] else #[0,3]) else (if j.val < 6 then #[0,0] else #[0,0,3])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[1] else (if j.val < 2 then #[0,1] else #[2,3,3])) else (if j.val < 5 then (if j.val < 4 then #[3] else #[3,3]) else (if j.val < 6 then #[3,7] else #[6,7,3])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 50).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 50).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 50) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D50

namespace D51

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 2570)) else (if j.val < 5 then (if j.val < 4 then 5140 else 10023) else (if j.val < 6 then 16660 else 34605)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 2048)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 51).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 51).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 2)) else (if j.val < 5 then (if j.val < 4 then 2 else 1) else (if j.val < 6 then 4 else 4)))

private def generatorRows (j : Fin 7) :
    Array (Fin 4) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,0] else #[0,3])) else (if j.val < 5 then (if j.val < 4 then #[0,3] else #[0]) else (if j.val < 6 then #[0,0,0,3] else #[0,0,0,3])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[1] else (if j.val < 2 then #[0,1] else #[2,2])) else (if j.val < 5 then (if j.val < 4 then #[3,2] else #[2]) else (if j.val < 6 then #[2,3,7,2] else #[3,6,7,2])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 51).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 51).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 51) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D51

namespace D52

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 3855)) else (if j.val < 5 then (if j.val < 4 then 4369 else 10023) else (if j.val < 6 then 17425 else 33320)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 2048)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 52).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 52).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 2)) else (if j.val < 5 then (if j.val < 4 then 2 else 1) else (if j.val < 6 then 2 else 4)))

private def generatorRows (j : Fin 7) :
    Array (Fin 4) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,0] else #[0,3])) else (if j.val < 5 then (if j.val < 4 then #[0,3] else #[0]) else (if j.val < 6 then #[0,3] else #[0,0,0,3])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[1] else (if j.val < 2 then #[0,1] else #[3,2])) else (if j.val < 5 then (if j.val < 4 then #[2,2] else #[2]) else (if j.val < 6 then #[7,2] else #[2,6,7,2])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 52).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 52).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 52) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D52

namespace D53

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 257 else 514) else (if j.val < 3 then 1028 else 2056)) else (if j.val < 6 then (if j.val < 5 then 4112 else 8224) else (if j.val < 7 then 16448 else 32896)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 256 else 512) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 53).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 53).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 4 else 3)) else (if j.val < 6 then (if j.val < 5 then 2 else 4) else (if j.val < 7 then 1 else 2)))

private def generatorRows (j : Fin 8) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1] else #[0,0,1]) else (if j.val < 3 then #[0,0,0,1] else #[0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1] else #[0,0,1,1]) else (if j.val < 7 then #[0] else #[0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,0,1] else #[0,1,0]) else (if j.val < 3 then #[0,1,2,0] else #[0,3,1])) else (if j.val < 6 then (if j.val < 5 then #[1,1] else #[0,1,0,1]) else (if j.val < 7 then #[7] else #[6,7])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 53).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 53).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 53) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D53

namespace D54

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 340 else 680) else (if j.val < 3 then 1105 else 2210)) else (if j.val < 6 then (if j.val < 5 then 4165 else 8330) else (if j.val < 7 then 16405 else 32810)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 256 else 512) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 54).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 54).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 4 else 3)) else (if j.val < 6 then (if j.val < 5 then 2 else 4) else (if j.val < 7 then 1 else 2)))

private def generatorRows (j : Fin 8) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1] else #[0,0,1]) else (if j.val < 3 then #[0,0,0,1] else #[0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1] else #[0,0,1,1]) else (if j.val < 7 then #[0] else #[0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,0,1] else #[0,1,0]) else (if j.val < 3 then #[0,1,2,0] else #[0,3,1])) else (if j.val < 6 then (if j.val < 5 then #[1,1] else #[0,1,0,1]) else (if j.val < 7 then #[7] else #[6,7])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 54).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 54).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 54) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D54

namespace D55

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 427 else 765) else (if j.val < 3 then 1198 else 2295)) else (if j.val < 6 then (if j.val < 5 then 4282 else 8415) else (if j.val < 7 then 16618 else 32895)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 256 else 512) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 55).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 55).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 4 else 3)) else (if j.val < 6 then (if j.val < 5 then 2 else 4) else (if j.val < 7 then 1 else 2)))

private def generatorRows (j : Fin 8) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1] else #[0,0,1]) else (if j.val < 3 then #[0,0,0,1] else #[0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1] else #[0,0,1,1]) else (if j.val < 7 then #[0] else #[0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,0,1] else #[0,1,0]) else (if j.val < 3 then #[0,1,2,0] else #[0,3,1])) else (if j.val < 6 then (if j.val < 5 then #[1,1] else #[0,1,0,1]) else (if j.val < 7 then #[7] else #[6,7])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 55).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 55).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 55) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D55

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

end
