import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 8–15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistry

local instance sourceGroupDisplacement8 : Group Source := PrimitiveAffineEightFrameTop15TopCertificate.group
local instance sourceInhabitedDisplacement8 : Inhabited Source := ⟨1⟩

namespace D8

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 1285 else 2570)) else (if j.val < 6 then (if j.val < 5 then 4369 else 8738) else (if j.val < 7 then 16660 else 33320)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 8).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 8).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 2) else (if j.val < 3 then 1 else 1)) else (if j.val < 6 then (if j.val < 5 then 1 else 2) else (if j.val < 7 then 2 else 3)))

private def generatorRows (j : Fin 8) :
    Array (Fin 5) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,2] else #[1,2]) else (if j.val < 3 then #[1] else #[1])) else (if j.val < 6 then (if j.val < 5 then #[3] else #[3,4]) else (if j.val < 7 then #[0,3] else #[0,3,4])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[4,4] else #[5,5]) else (if j.val < 3 then #[4] else #[5])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[5,4]) else (if j.val < 7 then #[4,5] else #[5,5,4])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 8).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 8).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow24ModuleRepresentation.representation PrimitiveAffineEightFrameTop15TopCertificate.ambient
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 8) displacementChart where
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
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 1285 else 2570)) else (if j.val < 6 then (if j.val < 5 then 4372 else 8744) else (if j.val < 7 then 16657 else 33314)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 9).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 9).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 2) else (if j.val < 3 then 1 else 1)) else (if j.val < 6 then (if j.val < 5 then 3 else 5) else (if j.val < 7 then 4 else 4)))

private def generatorRows (j : Fin 8) :
    Array (Fin 5) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,2] else #[1,2]) else (if j.val < 3 then #[1] else #[1])) else (if j.val < 6 then (if j.val < 5 then #[1,1,3] else #[0,1,1,3,4]) else (if j.val < 7 then #[0,1,1,3] else #[1,1,3,4])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[4,4] else #[5,5]) else (if j.val < 3 then #[4] else #[5])) else (if j.val < 6 then (if j.val < 5 then #[4,5,5] else #[5,4,5,5,4]) else (if j.val < 7 then #[4,4,5,5] else #[4,5,5,4])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 9).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 9).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow24ModuleRepresentation.representation PrimitiveAffineEightFrameTop15TopCertificate.ambient
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 9) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D9

namespace D10

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
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 10).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 10).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 3 else 5) else (if j.val < 3 then 3 else (if j.val < 4 then 5 else 2))) else (if j.val < 7 then (if j.val < 6 then 4 else 1) else (if j.val < 8 then 2 else (if j.val < 9 then 5 else 6))))

private def generatorRows (j : Fin 10) :
    Array (Fin 5) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1,1,3] else #[0,1,1,3,4]) else (if j.val < 3 then #[1,2,3] else (if j.val < 4 then #[0,1,2,3,4] else #[1,3]))) else (if j.val < 7 then (if j.val < 6 then #[0,1,3,4] else #[3]) else (if j.val < 8 then #[3,4] else (if j.val < 9 then #[0,1,1,3,3] else #[1,1,3,3,4,4]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[6,7,1] else #[7,6,7,1,0]) else (if j.val < 3 then #[7,6,1] else (if j.val < 4 then #[7,6,7,1,0] else #[7,1]))) else (if j.val < 7 then (if j.val < 6 then #[7,6,1,0] else #[7]) else (if j.val < 8 then #[7,6] else (if j.val < 9 then #[6,6,7,1,7] else #[6,7,1,7,0,6]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 10).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 10).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow24ModuleRepresentation.representation PrimitiveAffineEightFrameTop15TopCertificate.ambient
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 10) displacementChart where
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
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 5 else 10) else (if j.val < 3 then 80 else (if j.val < 4 then 160 else 1280))) else (if j.val < 7 then (if j.val < 6 then 2560 else 4369) else (if j.val < 8 then 8738 else (if j.val < 9 then 16657 else 33314))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 4 else 8) else (if j.val < 3 then 64 else (if j.val < 4 then 128 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 11).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 11).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 4 else (if j.val < 4 then 3 else 2))) else (if j.val < 7 then (if j.val < 6 then 2 else 1) else (if j.val < 8 then 2 else (if j.val < 9 then 3 else 4))))

private def generatorRows (j : Fin 10) :
    Array (Fin 5) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[1]) else (if j.val < 3 then #[0,1,2,2] else (if j.val < 4 then #[0,1,2] else #[0,1]))) else (if j.val < 7 then (if j.val < 6 then #[1,1] else #[3]) else (if j.val < 8 then #[3,3] else (if j.val < 9 then #[0,1,3] else #[0,1,3,3]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[4,7] else #[7]) else (if j.val < 3 then #[4,4,4,7] else (if j.val < 4 then #[4,4,4] else #[4,4]))) else (if j.val < 7 then (if j.val < 6 then #[7,8] else #[8]) else (if j.val < 8 then #[4,8] else (if j.val < 9 then #[7,7,8] else #[8,7,4,8]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 11).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 11).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow24ModuleRepresentation.representation PrimitiveAffineEightFrameTop15TopCertificate.ambient
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 11) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D11

namespace D12

private def displacementBasis (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 5 else 10) else (if j.val < 3 then 80 else (if j.val < 4 then 160 else 291))) else (if j.val < 8 then (if j.val < 6 then 1059 else (if j.val < 7 then 2560 else 4146)) else (if j.val < 9 then 8738 else (if j.val < 10 then 16434 else 33314))))

private def displacementDual (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 4 else 8) else (if j.val < 3 then 64 else (if j.val < 4 then 128 else 256))) else (if j.val < 8 then (if j.val < 6 then 1024 else (if j.val < 7 then 2048 else 4096)) else (if j.val < 9 then 8192 else (if j.val < 10 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 11 :=
  binaryCoordinateSpaceOfMasks 16 11
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 12).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 12).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 6 else (if j.val < 4 then 3 else 2))) else (if j.val < 8 then (if j.val < 6 then 4 else (if j.val < 7 then 2 else 2)) else (if j.val < 9 then 3 else (if j.val < 10 then 5 else 5))))

private def generatorRows (j : Fin 11) :
    Array (Fin 5) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,1,1,2,2] else (if j.val < 4 then #[0,1,2] else #[3,3]))) else (if j.val < 8 then (if j.val < 6 then #[0,1,3,3] else (if j.val < 7 then #[0,1] else #[3,3])) else (if j.val < 9 then #[3,3,3] else (if j.val < 10 then #[0,0,0,3,3] else #[0,0,3,3,3]))))

private def stateBasisRows (j : Fin 11) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[5] else #[4,5]) else (if j.val < 3 then #[4,5,4,5,4,5] else (if j.val < 4 then #[4,4,4] else #[4,9]))) else (if j.val < 8 then (if j.val < 6 then #[4,4,4,9] else (if j.val < 7 then #[5,5] else #[4,5])) else (if j.val < 9 then #[4,5,9] else (if j.val < 10 then #[4,5,8,4,5] else #[4,9,4,5,9]))))

private def termGenerator (j : Fin 11)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 11)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 11)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 12).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 12).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow24ModuleRepresentation.representation PrimitiveAffineEightFrameTop15TopCertificate.ambient
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 12) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D12

namespace D13

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
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 13).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 13).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 3)) else (if j.val < 4 then 6 else (if j.val < 5 then 1 else 3))) else (if j.val < 9 then (if j.val < 7 then 3 else (if j.val < 8 then 5 else 1)) else (if j.val < 10 then 4 else (if j.val < 11 then 3 else 7))))

private def generatorRows (j : Fin 12) :
    Array (Fin 5) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,1,2])) else (if j.val < 4 then #[0,0,1,1,2,2] else (if j.val < 5 then #[3] else #[3,3,4]))) else (if j.val < 9 then (if j.val < 7 then #[0,1,3] else (if j.val < 8 then #[0,1,3,3,4] else #[3])) else (if j.val < 10 then #[3,3,3,4] else (if j.val < 11 then #[0,0,3] else #[0,0,0,3,3,3,4]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 12) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[4,5] else (if j.val < 2 then #[4] else #[5,5,5])) else (if j.val < 4 then #[4,5,4,5,4,5] else (if j.val < 5 then #[9] else #[5,9,4]))) else (if j.val < 9 then (if j.val < 7 then #[4,4,9] else (if j.val < 8 then #[5,5,5,9,4] else #[5])) else (if j.val < 10 then #[4,5,9,4] else (if j.val < 11 then #[5,8,5] else #[4,5,9,4,5,9,4]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 13).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 13).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow24ModuleRepresentation.representation PrimitiveAffineEightFrameTop15TopCertificate.ambient
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 13) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D13

namespace D14

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
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 14).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 14).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 1)) else (if j.val < 4 then 3 else (if j.val < 5 then 1 else 3))) else (if j.val < 9 then (if j.val < 7 then 3 else (if j.val < 8 then 6 else 2)) else (if j.val < 10 then 1 else (if j.val < 11 then 4 else 2))))

private def generatorRows (j : Fin 12) :
    Array (Fin 5) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,0] else #[2])) else (if j.val < 4 then #[0,1,2] else (if j.val < 5 then #[3] else #[3,3,4]))) else (if j.val < 9 then (if j.val < 7 then #[0,1,3] else (if j.val < 8 then #[0,0,1,3,3,4] else #[3,3])) else (if j.val < 10 then #[4] else (if j.val < 11 then #[0,0,3,3] else #[0,4]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 13) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[2] else (if j.val < 2 then #[2,5] else #[2])) else (if j.val < 4 then #[5,5,5] else (if j.val < 5 then #[6] else #[2,5,2]))) else (if j.val < 9 then (if j.val < 7 then #[5,5,6] else (if j.val < 8 then #[2,5,6,2,5,2] else #[2,6])) else (if j.val < 10 then #[2] else (if j.val < 11 then #[5,9,2,6] else #[10,2]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 13 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 14).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 14).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow24ModuleRepresentation.representation PrimitiveAffineEightFrameTop15TopCertificate.ambient
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 14) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D14

namespace D15

private def displacementBasis (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 10 else 17)) else (if j.val < 4 then 65 else (if j.val < 5 then 160 else 291))) else (if j.val < 9 then (if j.val < 7 then 514 else (if j.val < 8 then 1059 else 2050)) else (if j.val < 11 then (if j.val < 10 then 4131 else 8224) else (if j.val < 12 then 16419 else 32800))))

private def displacementDual (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 8 else 16)) else (if j.val < 4 then 64 else (if j.val < 5 then 128 else 256))) else (if j.val < 9 then (if j.val < 7 then 512 else (if j.val < 8 then 1024 else 2048)) else (if j.val < 11 then (if j.val < 10 then 4096 else 8192) else (if j.val < 12 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 13 :=
  binaryCoordinateSpaceOfMasks 16 13
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 15).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 15).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 1 else 1)) else (if j.val < 4 then 2 else (if j.val < 5 then 1 else 2))) else (if j.val < 9 then (if j.val < 7 then 3 else (if j.val < 8 then 4 else 5)) else (if j.val < 11 then (if j.val < 10 then 2 else 2) else (if j.val < 12 then 4 else 4))))

private def generatorRows (j : Fin 13) :
    Array (Fin 5) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0] else #[3])) else (if j.val < 4 then #[2,3] else (if j.val < 5 then #[2] else #[3,3]))) else (if j.val < 9 then (if j.val < 7 then #[3,3,4] else (if j.val < 8 then #[0,1,3,3] else #[0,1,3,3,4])) else (if j.val < 11 then (if j.val < 10 then #[3,3] else #[3,4]) else (if j.val < 12 then #[0,0,3,3] else #[0,0,3,4]))))

private def stateBasisRows (j : Fin 13) :
    Array (Fin 14) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[2] else (if j.val < 2 then #[3] else #[6])) else (if j.val < 4 then #[2,6] else (if j.val < 5 then #[3] else #[6,7]))) else (if j.val < 9 then (if j.val < 7 then #[2,3,2] else (if j.val < 8 then #[2,6,6,7] else #[3,7,2,3,2])) else (if j.val < 11 then (if j.val < 10 then #[2,7] else #[6,2]) else (if j.val < 12 then #[2,10,2,7] else #[3,11,6,2]))))

private def termGenerator (j : Fin 13)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 13)
    (t : Fin (termCount j)) : Fin 14 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 13)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 15).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 15).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow24ModuleRepresentation.representation PrimitiveAffineEightFrameTop15TopCertificate.ambient
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 15) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D15

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistry

end
