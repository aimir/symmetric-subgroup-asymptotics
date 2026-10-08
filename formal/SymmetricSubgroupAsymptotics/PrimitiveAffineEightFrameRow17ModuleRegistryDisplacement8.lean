import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 8–11. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistry

local instance sourceGroupDisplacement8 : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group
local instance sourceInhabitedDisplacement8 : Inhabited Source := ⟨1⟩

namespace D8

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
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 8).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 8).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 1 else 3) else (if j.val < 7 then 2 else (if j.val < 8 then 4 else 2))))

private def generatorRows (j : Fin 9) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[1]) else (if j.val < 3 then #[0,0,1] else #[0,1])) else (if j.val < 6 then (if j.val < 5 then #[7] else #[0,4,7]) else (if j.val < 7 then #[4,7] else (if j.val < 8 then #[0,0,4,7] else #[0,4]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,0] else #[0]) else (if j.val < 3 then #[1,3,3] else #[1,3])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[6,5,0]) else (if j.val < 7 then #[5,0] else (if j.val < 8 then #[6,8,8,0] else #[6,8]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 8 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 8).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 8).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow17ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 8) displacementChart where
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
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 15 else 20) else (if j.val < 3 then 34 else (if j.val < 4 then 65 else 135))) else (if j.val < 7 then (if j.val < 6 then 3840 else 5120) else (if j.val < 8 then 8704 else (if j.val < 9 then 16640 else 34560))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 8 else 16) else (if j.val < 3 then 32 else (if j.val < 4 then 64 else 128))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 9).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 9).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 3) else (if j.val < 3 then 2 else (if j.val < 4 then 4 else 2))) else (if j.val < 7 then (if j.val < 6 then 2 else 3) else (if j.val < 8 then 3 else (if j.val < 9 then 4 else 3))))

private def generatorRows (j : Fin 10) :
    Array (Fin 8) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[7] else #[0,1,7]) else (if j.val < 3 then #[1,7] else (if j.val < 4 then #[0,0,1,7] else #[0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,7] else #[0,4,7]) else (if j.val < 8 then #[0,4,7] else (if j.val < 9 then #[0,0,4,7] else #[0,0,4]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[5] else #[1,0,5]) else (if j.val < 3 then #[0,5] else (if j.val < 4 then #[1,3,3,5] else #[1,3]))) else (if j.val < 7 then (if j.val < 6 then #[5,5] else #[5,6,5]) else (if j.val < 8 then #[7,6,5] else (if j.val < 9 then #[7,9,9,5] else #[5,7,9]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 8 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 9).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 9).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow17ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 9) displacementChart where
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
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 15 else 20) else (if j.val < 3 then 34 else (if j.val < 4 then 65 else 135))) else (if j.val < 8 then (if j.val < 6 then 1285 else (if j.val < 7 then 2565 else 4357)) else (if j.val < 9 then 8704 else (if j.val < 10 then 16640 else 33285))))

private def displacementDual (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 8 else 16) else (if j.val < 3 then 32 else (if j.val < 4 then 64 else 128))) else (if j.val < 8 then (if j.val < 6 then 1024 else (if j.val < 7 then 2048 else 4096)) else (if j.val < 9 then 8192 else (if j.val < 10 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 11 :=
  binaryCoordinateSpaceOfMasks 16 11
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 10).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 10).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 2 else (if j.val < 4 then 3 else 3))) else (if j.val < 8 then (if j.val < 6 then 1 else (if j.val < 7 then 2 else 3)) else (if j.val < 9 then 2 else (if j.val < 10 then 3 else 4))))

private def generatorRows (j : Fin 11) :
    Array (Fin 8) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,1]) else (if j.val < 3 then #[0,1] else (if j.val < 4 then #[0,0,1] else #[0,0,1]))) else (if j.val < 8 then (if j.val < 6 then #[7] else (if j.val < 7 then #[0,7] else #[0,4,7])) else (if j.val < 9 then #[0,4] else (if j.val < 10 then #[0,0,4] else #[0,0,4,7]))))

private def stateBasisRows (j : Fin 11) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,1]) else (if j.val < 3 then #[2,1] else (if j.val < 4 then #[2,4,4] else #[0,2,4]))) else (if j.val < 8 then (if j.val < 6 then #[0] else (if j.val < 7 then #[6,0] else #[6,7,0])) else (if j.val < 9 then #[8,7] else (if j.val < 10 then #[8,10,10] else #[6,8,10,0]))))

private def termGenerator (j : Fin 11)
    (t : Fin (termCount j)) : Fin 8 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 11)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 11)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 10).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 10).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow17ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 10) displacementChart where
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
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 11).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 11).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 16) : ℕ :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 4) else (if j.val < 3 then 5 else 3)) else (if j.val < 6 then (if j.val < 5 then 3 else 2) else (if j.val < 7 then 2 else 1))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 2 else 4) else (if j.val < 11 then 5 else 3)) else (if j.val < 14 then (if j.val < 13 then 3 else 2) else (if j.val < 15 then 2 else 1))))

private def generatorRows (j : Fin 16) :
    Array (Fin 8) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0,1,1,2]) else (if j.val < 3 then #[0,0,1,1,2] else #[0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1,2] else #[1,2]) else (if j.val < 7 then #[0,1] else #[1]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[0,4] else #[0,4,4,5]) else (if j.val < 11 then #[0,0,4,4,5] else #[0,0,4])) else (if j.val < 14 then (if j.val < 13 then #[0,4,5] else #[4,5]) else (if j.val < 15 then #[0,4] else #[4]))))

private def stateBasisRows (j : Fin 16) :
    Array (Fin 16) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[4,0] else #[4,0,1,0]) else (if j.val < 3 then #[1,4,0,1,0] else #[0,4,0])) else (if j.val < 6 then (if j.val < 5 then #[4,0,0] else #[0,0]) else (if j.val < 7 then #[6,6] else #[6]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[12,8] else #[12,8,9,8]) else (if j.val < 11 then #[9,12,8,9,8] else #[8,12,8])) else (if j.val < 14 then (if j.val < 13 then #[12,8,8] else #[8,8]) else (if j.val < 15 then #[14,14] else #[14]))))

private def termGenerator (j : Fin 16)
    (t : Fin (termCount j)) : Fin 8 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 16)
    (t : Fin (termCount j)) : Fin 16 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 16)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 11).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 11).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow17ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 11) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D11

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistry

end
