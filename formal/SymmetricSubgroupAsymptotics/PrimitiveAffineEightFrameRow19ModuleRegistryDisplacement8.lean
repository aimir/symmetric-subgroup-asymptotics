import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 8–11. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistry

local instance sourceGroupDisplacement8 : Group Source := PrimitiveAffineEightFrameTop10TopCertificate.group
local instance sourceInhabitedDisplacement8 : Inhabited Source := ⟨1⟩

namespace D8

private def displacementBasis (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 30 else 39) else (if j.val < 3 then 75 else 141)) else (if j.val < 6 then (if j.val < 5 then 3855 else 4367) else (if j.val < 7 then 9984 else (if j.val < 8 then 17423 else 33295))))

private def displacementDual (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else 128)) else (if j.val < 6 then (if j.val < 5 then 2048 else 4096) else (if j.val < 7 then 8192 else (if j.val < 8 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 9 :=
  binaryCoordinateSpaceOfMasks 16 9
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 8).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 8).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 1 else 2) else (if j.val < 7 then 2 else (if j.val < 8 then 3 else 4))))

private def generatorRows (j : Fin 9) :
    Array (Fin 9) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0] else #[0,0,0])) else (if j.val < 6 then (if j.val < 5 then #[8] else #[3,8]) else (if j.val < 7 then #[3,3] else (if j.val < 8 then #[3,3,8] else #[3,3,3,8]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,1]) else (if j.val < 3 then #[1,4] else #[1,3,4])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[5,0]) else (if j.val < 7 then #[5,6] else (if j.val < 8 then #[6,9,0] else #[6,8,9,0]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 9 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 8).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 8).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow19ModuleRepresentation.representation PrimitiveAffineEightFrameTop10TopCertificate.ambient
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 8) displacementChart where
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
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 15 else 17) else (if j.val < 3 then 39 else (if j.val < 4 then 68 else 130))) else (if j.val < 7 then (if j.val < 6 then 3840 else 4352) else (if j.val < 8 then 9984 else (if j.val < 9 then 17408 else 33280))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 8 else 16) else (if j.val < 3 then 32 else (if j.val < 4 then 64 else 128))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 9).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 9).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 2 else (if j.val < 4 then 3 else 4))) else (if j.val < 7 then (if j.val < 6 then 1 else 3) else (if j.val < 8 then 1 else (if j.val < 9 then 3 else 5))))

private def generatorRows (j : Fin 10) :
    Array (Fin 9) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[7] else #[0,7]) else (if j.val < 3 then #[0,0] else (if j.val < 4 then #[0,0,7] else #[0,0,0,7]))) else (if j.val < 7 then (if j.val < 6 then #[6] else #[3,3,6]) else (if j.val < 8 then #[3] else (if j.val < 9 then #[3,3,6] else #[3,3,3,3,6]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[5] else #[0,5]) else (if j.val < 3 then #[0,1] else (if j.val < 4 then #[1,4,5] else #[1,3,4,5]))) else (if j.val < 7 then (if j.val < 6 then #[5] else #[5,6,5]) else (if j.val < 8 then #[5] else (if j.val < 9 then #[6,10,5] else #[5,6,9,10,5]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 9 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 9).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 9).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow19ModuleRepresentation.representation PrimitiveAffineEightFrameTop10TopCertificate.ambient
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 9) displacementChart where
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
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 15 else 17) else (if j.val < 3 then 39 else (if j.val < 4 then 68 else 130))) else (if j.val < 8 then (if j.val < 6 then 1285 else (if j.val < 7 then 2565 else 4352)) else (if j.val < 9 then 8709 else (if j.val < 10 then 16645 else 33280))))

private def displacementDual (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 8 else 16) else (if j.val < 3 then 32 else (if j.val < 4 then 64 else 128))) else (if j.val < 8 then (if j.val < 6 then 1024 else (if j.val < 7 then 2048 else 4096)) else (if j.val < 9 then 8192 else (if j.val < 10 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 11 :=
  binaryCoordinateSpaceOfMasks 16 11
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 10).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 10).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 3) else (if j.val < 3 then 1 else (if j.val < 4 then 3 else 5))) else (if j.val < 8 then (if j.val < 6 then 1 else (if j.val < 7 then 2 else 3)) else (if j.val < 9 then 2 else (if j.val < 10 then 4 else 5))))

private def generatorRows (j : Fin 11) :
    Array (Fin 9) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[7] else #[0,0,7]) else (if j.val < 3 then #[0] else (if j.val < 4 then #[0,0,7] else #[0,0,0,0,7]))) else (if j.val < 8 then (if j.val < 6 then #[8] else (if j.val < 7 then #[6,8] else #[3,3,6])) else (if j.val < 9 then #[3,8] else (if j.val < 10 then #[3,3,6,8] else #[3,3,3,3,6]))))

private def stateBasisRows (j : Fin 11) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,1,0]) else (if j.val < 3 then #[0] else (if j.val < 4 then #[1,5,0] else #[0,1,4,5,0]))) else (if j.val < 8 then (if j.val < 6 then #[0] else (if j.val < 7 then #[6,0] else #[6,7,6])) else (if j.val < 9 then #[6,0] else (if j.val < 10 then #[7,11,6,0] else #[6,7,10,11,6]))))

private def termGenerator (j : Fin 11)
    (t : Fin (termCount j)) : Fin 9 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 11)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 11)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 10).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 10).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow19ModuleRepresentation.representation PrimitiveAffineEightFrameTop10TopCertificate.ambient
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 10) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D10

namespace D11

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
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 11).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 11).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 16) : ℕ :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 4 else 3)) else (if j.val < 6 then (if j.val < 5 then 2 else 4) else (if j.val < 7 then 1 else 2))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 3 else 3) else (if j.val < 11 then 4 else 3)) else (if j.val < 14 then (if j.val < 13 then 2 else 4) else (if j.val < 15 then 1 else 2))))

private def generatorRows (j : Fin 16) :
    Array (Fin 9) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1] else #[0,0,1]) else (if j.val < 3 then #[0,0,0,1] else #[0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1] else #[0,0,1,1]) else (if j.val < 7 then #[0] else #[0,0]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[3,4,4] else #[3,3,4]) else (if j.val < 11 then #[3,3,3,4] else #[3,3,4])) else (if j.val < 14 then (if j.val < 13 then #[3,4] else #[3,3,4,4]) else (if j.val < 15 then #[3] else #[3,3]))))

private def stateBasisRows (j : Fin 16) :
    Array (Fin 16) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,0,1] else #[0,1,0]) else (if j.val < 3 then #[0,1,2,0] else #[0,3,1])) else (if j.val < 6 then (if j.val < 5 then #[1,1] else #[0,1,0,1]) else (if j.val < 7 then #[7] else #[6,7]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[9,8,9] else #[8,9,8]) else (if j.val < 11 then #[8,9,10,8] else #[8,11,9])) else (if j.val < 14 then (if j.val < 13 then #[9,9] else #[8,9,8,9]) else (if j.val < 15 then #[15] else #[14,15]))))

private def termGenerator (j : Fin 16)
    (t : Fin (termCount j)) : Fin 9 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 16)
    (t : Fin (termCount j)) : Fin 16 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 16)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 11).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 11).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow19ModuleRepresentation.representation PrimitiveAffineEightFrameTop10TopCertificate.ambient
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 11) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D11

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistry

end
