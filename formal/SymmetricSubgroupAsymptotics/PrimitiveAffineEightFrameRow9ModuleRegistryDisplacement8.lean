import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 8–15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistry

local instance sourceGroupDisplacement8 : Group Source := PrimitiveAffineEightFrameRow9TopCertificate.group
local instance sourceInhabitedDisplacement8 : Inhabited Source := ⟨1⟩

namespace D8

private def displacementBasis (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 14649 else (if j.val < 4 then 21760 else 37689)))

private def displacementDual (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 8192 else (if j.val < 4 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 5 :=
  binaryCoordinateSpaceOfMasks 16 5
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 8).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 8).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 1 else (if j.val < 4 then 3 else 2)))

private def generatorRows (j : Fin 5) :
    Array (Fin 7) :=
  (if j.val < 2 then (if j.val < 1 then #[0,1] else #[1]) else (if j.val < 3 then #[0] else (if j.val < 4 then #[0,0,1] else #[0,1])))

private def stateBasisRows (j : Fin 5) :
    Array (Fin 7) :=
  (if j.val < 2 then (if j.val < 1 then #[1,1] else #[1]) else (if j.val < 3 then #[3] else (if j.val < 4 then #[3,5,5] else #[3,5])))

private def termGenerator (j : Fin 5)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 5)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 5)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 8).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 8).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation PrimitiveAffineEightFrameRow9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 8) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D8

namespace D9

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 6939)) else (if j.val < 4 then 11565 else (if j.val < 5 then 19995 else 34605)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 9).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 9).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 2)) else (if j.val < 4 then 1 else (if j.val < 5 then 3 else 2)))

private def generatorRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[1] else #[0,1])) else (if j.val < 4 then #[1] else (if j.val < 5 then #[0,0,1] else #[0,1])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[3,2])) else (if j.val < 4 then #[2] else (if j.val < 5 then #[3,5,5] else #[3,5])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 9).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 9).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation PrimitiveAffineEightFrameRow9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 9) displacementChart where
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
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 27 else 45) else (if j.val < 3 then 78 else 135)) else (if j.val < 6 then (if j.val < 5 then 6912 else 11520) else (if j.val < 7 then 19968 else 34560)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else 128)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 10).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 10).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 1 else 2) else (if j.val < 7 then 3 else 2)))

private def generatorRows (j : Fin 8) :
    Array (Fin 7) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[0,1,1] else #[1,1])) else (if j.val < 6 then (if j.val < 5 then #[1] else #[0,1]) else (if j.val < 7 then #[0,1,1] else #[1,1])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[2,1,2] else #[1,2])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[4,5]) else (if j.val < 7 then #[6,5,6] else #[5,6])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 10).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 10).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation PrimitiveAffineEightFrameRow9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 10) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D10

namespace D11

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 57 else (if j.val < 2 then 85 else 147)) else (if j.val < 5 then (if j.val < 4 then 7710 else 10014) else (if j.val < 6 then 19230 else 36126)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 32 else (if j.val < 2 then 64 else 128)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 11).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 11).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 3 else 2)) else (if j.val < 5 then (if j.val < 4 then 1 else 2) else (if j.val < 6 then 4 else 3)))

private def generatorRows (j : Fin 7) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,0,1] else #[0,1])) else (if j.val < 5 then (if j.val < 4 then #[6] else #[0,6]) else (if j.val < 6 then #[0,0,1,6] else #[0,1,6])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,2,2] else #[0,2])) else (if j.val < 5 then (if j.val < 4 then #[0] else #[4,0]) else (if j.val < 6 then #[4,6,6,0] else #[4,6,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 11).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 11).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation PrimitiveAffineEightFrameRow9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 11) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D11

namespace D12

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
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 12).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 12).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 2)) else (if j.val < 5 then (if j.val < 4 then 2 else 3) else (if j.val < 6 then 3 else 2)))

private def generatorRows (j : Fin 7) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[1] else #[0,6])) else (if j.val < 5 then (if j.val < 4 then #[1,6] else #[0,1,6]) else (if j.val < 6 then #[0,1,6] else #[0,1])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[1,1] else (if j.val < 2 then #[1] else #[4,0])) else (if j.val < 5 then (if j.val < 4 then #[3,0] else #[4,3,0]) else (if j.val < 6 then #[6,6,0] else #[4,6])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 12).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 12).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation PrimitiveAffineEightFrameRow9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 12) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D12

namespace D13

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
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 13).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 13).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 1)) else (if j.val < 5 then (if j.val < 4 then 2 else 2) else (if j.val < 6 then 3 else 3)))

private def generatorRows (j : Fin 7) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[1] else #[0])) else (if j.val < 5 then (if j.val < 4 then #[0,1] else #[0,1]) else (if j.val < 6 then #[0,0,1] else #[0,0,1])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[2])) else (if j.val < 5 then (if j.val < 4 then #[2,3] else #[4,3]) else (if j.val < 6 then #[4,6,6] else #[2,4,6])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 13).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 13).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation PrimitiveAffineEightFrameRow9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 13) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D13

namespace D14

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
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 14).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 14).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 1)) else (if j.val < 5 then (if j.val < 4 then 2 else 2) else (if j.val < 6 then 3 else 3)))

private def generatorRows (j : Fin 7) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[1] else #[0])) else (if j.val < 5 then (if j.val < 4 then #[0,1] else #[0,1]) else (if j.val < 6 then #[0,0,1] else #[0,0,1])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[2])) else (if j.val < 5 then (if j.val < 4 then #[2,3] else #[4,3]) else (if j.val < 6 then #[4,6,6] else #[2,4,6])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 14).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 14).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation PrimitiveAffineEightFrameRow9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 14) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D14

namespace D15

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 27 else 45) else (if j.val < 3 then 78 else 135)) else (if j.val < 6 then (if j.val < 5 then 6912 else 11520) else (if j.val < 7 then 19968 else 34560)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else 128)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 15).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 15).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 4 else 3) else (if j.val < 7 then 5 else 4)))

private def generatorRows (j : Fin 8) :
    Array (Fin 7) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[0,1,1] else #[1,1])) else (if j.val < 6 then (if j.val < 5 then #[0,0,1,1] else #[0,1,1]) else (if j.val < 7 then #[0,0,0,1,1] else #[0,0,1,1])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 9) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[2,1,2] else #[1,2])) else (if j.val < 6 then (if j.val < 5 then #[0,5,1,4] else #[0,1,4]) else (if j.val < 7 then #[0,5,7,1,7] else #[0,5,1,7])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 7 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 15).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow9ModuleRepresentation.charts 15).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation PrimitiveAffineEightFrameRow9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states 15) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D15

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistry

end
