import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 8–14. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistry

local instance sourceGroupDisplacement8 : Group Source := PrimitiveAffineEightFrameTop17TopCertificate.group
local instance sourceInhabitedDisplacement8 : Inhabited Source := ⟨1⟩

namespace D8

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
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 8).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 8).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 1) else (if j.val < 3 then 1 else (if j.val < 4 then 1 else 1))) else (if j.val < 7 then (if j.val < 6 then 1 else 2) else (if j.val < 8 then 1 else (if j.val < 9 then 3 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 6) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1] else #[1]) else (if j.val < 3 then #[3] else (if j.val < 4 then #[3] else #[2]))) else (if j.val < 7 then (if j.val < 6 then #[2] else #[4,5]) else (if j.val < 8 then #[5] else (if j.val < 9 then #[0,4,5] else #[0,5]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[6] else #[7]) else (if j.val < 3 then #[6] else (if j.val < 4 then #[7] else #[6]))) else (if j.val < 7 then (if j.val < 6 then #[7] else #[6,6]) else (if j.val < 8 then #[6] else (if j.val < 9 then #[6,6,6] else #[7,6]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 8).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 8).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow26ModuleRepresentation.representation PrimitiveAffineEightFrameTop17TopCertificate.ambient
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 8) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D8

namespace D9

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
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 9).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 9).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 1) else (if j.val < 3 then 1 else (if j.val < 4 then 2 else 1))) else (if j.val < 7 then (if j.val < 6 then 2 else 2) else (if j.val < 8 then 1 else (if j.val < 9 then 3 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 6) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1] else #[1]) else (if j.val < 3 then #[3] else (if j.val < 4 then #[3,3] else #[2]))) else (if j.val < 7 then (if j.val < 6 then #[2,2] else #[4,4]) else (if j.val < 8 then #[4] else (if j.val < 9 then #[0,4,4] else #[0,4]))))

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
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 9).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 9).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow26ModuleRepresentation.representation PrimitiveAffineEightFrameTop17TopCertificate.ambient
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 9) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D9

namespace D10

private def displacementBasis (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 5 else 10) else (if j.val < 3 then 80 else (if j.val < 4 then 160 else 786))) else (if j.val < 8 then (if j.val < 6 then 1280 else (if j.val < 7 then 2322 else 4369)) else (if j.val < 9 then 8496 else (if j.val < 10 then 16657 else 33072))))

private def displacementDual (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 4 else 8) else (if j.val < 3 then 64 else (if j.val < 4 then 128 else 512))) else (if j.val < 8 then (if j.val < 6 then 1024 else (if j.val < 7 then 2048 else 4096)) else (if j.val < 9 then 8192 else (if j.val < 10 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 11 :=
  binaryCoordinateSpaceOfMasks 16 11
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 10).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 10).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 2 else (if j.val < 4 then 1 else 3))) else (if j.val < 8 then (if j.val < 6 then 1 else (if j.val < 7 then 4 else 2)) else (if j.val < 9 then 1 else (if j.val < 10 then 3 else 2))))

private def generatorRows (j : Fin 11) :
    Array (Fin 6) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1] else #[1,1]) else (if j.val < 3 then #[3,3] else (if j.val < 4 then #[3] else #[4,4,4]))) else (if j.val < 8 then (if j.val < 6 then #[2] else (if j.val < 7 then #[2,4,4,4] else #[4,4])) else (if j.val < 9 then #[4] else (if j.val < 10 then #[0,4,4] else #[0,4]))))

private def stateBasisRows (j : Fin 11) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[5] else #[4,5]) else (if j.val < 3 then #[4,5] else (if j.val < 4 then #[4] else #[4,5,8]))) else (if j.val < 8 then (if j.val < 6 then #[4] else (if j.val < 7 then #[5,4,5,8] else #[5,8])) else (if j.val < 9 then #[8] else (if j.val < 10 then #[8,5,8] else #[9,8]))))

private def termGenerator (j : Fin 11)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 11)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 11)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 10).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 10).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow26ModuleRepresentation.representation PrimitiveAffineEightFrameTop17TopCertificate.ambient
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 10) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D10

namespace D11

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
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 11).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 11).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 1)) else (if j.val < 4 then 2 else (if j.val < 5 then 3 else 4))) else (if j.val < 9 then (if j.val < 7 then 4 else (if j.val < 8 then 5 else 1)) else (if j.val < 10 then 2 else (if j.val < 11 then 2 else 3))))

private def generatorRows (j : Fin 12) :
    Array (Fin 6) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[1,1] else (if j.val < 2 then #[1] else #[3])) else (if j.val < 4 then #[3,3] else (if j.val < 5 then #[4,4,5] else #[4,4,4,5]))) else (if j.val < 9 then (if j.val < 7 then #[2,4,4,5] else (if j.val < 8 then #[2,4,4,4,5] else #[5])) else (if j.val < 10 then #[4,5] else (if j.val < 11 then #[0,5] else #[0,4,5]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 12) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[4,5] else (if j.val < 2 then #[4] else #[5])) else (if j.val < 4 then #[4,5] else (if j.val < 5 then #[4,5,5] else #[4,5,8,5]))) else (if j.val < 9 then (if j.val < 7 then #[4,4,5,5] else (if j.val < 8 then #[5,4,5,8,5] else #[5])) else (if j.val < 10 then #[4,5] else (if j.val < 11 then #[8,5] else #[9,4,5]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 11).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 11).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow26ModuleRepresentation.representation PrimitiveAffineEightFrameTop17TopCertificate.ambient
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 11) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D11

namespace D12

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
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 12).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 12).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 1)) else (if j.val < 4 then 2 else (if j.val < 5 then 4 else 3))) else (if j.val < 9 then (if j.val < 7 then 5 else (if j.val < 8 then 4 else 1)) else (if j.val < 10 then 3 else (if j.val < 11 then 2 else 4))))

private def generatorRows (j : Fin 12) :
    Array (Fin 6) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[1] else (if j.val < 2 then #[1,1] else #[3])) else (if j.val < 4 then #[3,3] else (if j.val < 5 then #[4,4,4,5] else #[4,4,5]))) else (if j.val < 9 then (if j.val < 7 then #[2,4,4,4,5] else (if j.val < 8 then #[2,4,4,5] else #[5])) else (if j.val < 10 then #[4,4,5] else (if j.val < 11 then #[0,5] else #[0,4,4,5]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 13) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[5] else (if j.val < 2 then #[2,5] else #[6])) else (if j.val < 4 then #[2,6] else (if j.val < 5 then #[2,5,6,2] else #[2,6,2]))) else (if j.val < 9 then (if j.val < 7 then #[5,2,5,6,2] else (if j.val < 8 then #[6,2,6,2] else #[2])) else (if j.val < 10 then #[2,5,2] else (if j.val < 11 then #[9,2] else #[10,2,5,2]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 13 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 12).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 12).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow26ModuleRepresentation.representation PrimitiveAffineEightFrameTop17TopCertificate.ambient
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 12) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D12

namespace D13

private def displacementBasis (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 10 else 51)) else (if j.val < 4 then 80 else (if j.val < 5 then 147 else 257))) else (if j.val < 9 then (if j.val < 7 then 531 else (if j.val < 8 then 1025 else 2067)) else (if j.val < 11 then (if j.val < 10 then 4112 else 8194) else (if j.val < 12 then 16400 else 32770))))

private def displacementDual (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 8 else 32)) else (if j.val < 4 then 64 else (if j.val < 5 then 128 else 256))) else (if j.val < 9 then (if j.val < 7 then 512 else (if j.val < 8 then 1024 else 2048)) else (if j.val < 11 then (if j.val < 10 then 4096 else 8192) else (if j.val < 12 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 13 :=
  binaryCoordinateSpaceOfMasks 16 13
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 13).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 13).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 1 else 2)) else (if j.val < 4 then 1 else (if j.val < 5 then 3 else 3))) else (if j.val < 9 then (if j.val < 7 then 2 else (if j.val < 8 then 4 else 3)) else (if j.val < 11 then (if j.val < 10 then 4 else 1) else (if j.val < 12 then 5 else 2))))

private def generatorRows (j : Fin 13) :
    Array (Fin 6) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[1] else (if j.val < 2 then #[1] else #[4,4])) else (if j.val < 4 then #[3] else (if j.val < 5 then #[3,4,4] else #[4,4,5]))) else (if j.val < 9 then (if j.val < 7 then #[4,5] else (if j.val < 8 then #[2,4,4,5] else #[2,4,5])) else (if j.val < 11 then (if j.val < 10 then #[4,4,4,5] else #[5]) else (if j.val < 12 then #[0,4,4,4,5] else #[0,5]))))

private def stateBasisRows (j : Fin 13) :
    Array (Fin 14) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[2] else (if j.val < 2 then #[3] else #[6,7])) else (if j.val < 4 then #[2] else (if j.val < 5 then #[3,6,7] else #[2,7,3]))) else (if j.val < 9 then (if j.val < 7 then #[2,3] else (if j.val < 8 then #[6,2,7,3] else #[7,2,3])) else (if j.val < 11 then (if j.val < 10 then #[2,3,6,3] else #[3]) else (if j.val < 12 then #[10,2,3,6,3] else #[11,3]))))

private def termGenerator (j : Fin 13)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 13)
    (t : Fin (termCount j)) : Fin 14 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 13)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 13).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 13).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow26ModuleRepresentation.representation PrimitiveAffineEightFrameTop17TopCertificate.ambient
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 13) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D13

namespace D14

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
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 14).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 14).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 16) : ℕ :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 5 else 7) else (if j.val < 3 then 6 else 8)) else (if j.val < 6 then (if j.val < 5 then 7 else 5) else (if j.val < 7 then 8 else 6))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 6 else 6) else (if j.val < 11 then 7 else 7)) else (if j.val < 14 then (if j.val < 13 then 4 else 8) else (if j.val < 15 then 5 else 9))))

private def generatorRows (j : Fin 16) :
    Array (Fin 6) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[4,4,4,5,5] else #[4,4,4,4,4,4,5]) else (if j.val < 3 then #[1,4,4,4,5,5] else #[1,4,4,4,4,4,4,5])) else (if j.val < 6 then (if j.val < 5 then #[4,4,4,4,4,5,5] else #[4,4,4,4,5]) else (if j.val < 7 then #[3,4,4,4,4,4,5,5] else #[3,4,4,4,4,5]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[4,4,4,4,4,5] else #[4,4,4,4,5,5]) else (if j.val < 11 then #[2,4,4,4,4,4,5] else #[2,4,4,4,4,5,5])) else (if j.val < 14 then (if j.val < 13 then #[4,4,4,5] else #[4,4,4,4,4,4,5,5]) else (if j.val < 15 then #[0,4,4,4,5] else #[0,4,4,4,4,4,4,5,5]))))

private def stateBasisRows (j : Fin 16) :
    Array (Fin 16) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,5,8,0,1] else #[0,1,4,5,8,9,0]) else (if j.val < 3 then #[0,1,5,8,0,1] else #[1,0,1,4,5,8,9,0])) else (if j.val < 6 then (if j.val < 5 then #[0,1,5,8,9,0,1] else #[0,4,5,9,0]) else (if j.val < 7 then #[4,0,1,5,8,9,0,1] else #[5,0,4,5,9,0]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[0,4,5,8,9,0] else #[0,1,5,8,0,1]) else (if j.val < 11 then #[8,0,4,5,8,9,0] else #[9,0,1,5,8,0,1])) else (if j.val < 14 then (if j.val < 13 then #[0,4,9,0] else #[0,1,4,5,8,9,0,1]) else (if j.val < 15 then #[12,0,4,9,0] else #[13,0,1,4,5,8,9,0,1]))))

private def termGenerator (j : Fin 16)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 16)
    (t : Fin (termCount j)) : Fin 16 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 16)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 14).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 14).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow26ModuleRepresentation.representation PrimitiveAffineEightFrameTop17TopCertificate.ambient
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 14) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D14

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistry

end
