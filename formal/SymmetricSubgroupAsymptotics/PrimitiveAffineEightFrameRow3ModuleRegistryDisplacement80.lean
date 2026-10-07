import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 80–82. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistry

local instance sourceGroupDisplacement80 : Group Source := PrimitiveAffineEightFrameRow3TopCertificate.group
local instance sourceInhabitedDisplacement80 : Inhabited Source := ⟨1⟩

namespace D80

private def displacementBasis (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 10 else 17)) else (if j.val < 5 then (if j.val < 4 then 34 else 65) else (if j.val < 6 then 130 else 258))) else (if j.val < 10 then (if j.val < 8 then 513 else (if j.val < 9 then 1026 else 2049)) else (if j.val < 12 then (if j.val < 11 then 4098 else 8193) else (if j.val < 13 then 16386 else 32769))))

private def displacementDual (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 8 else 16)) else (if j.val < 5 then (if j.val < 4 then 32 else 64) else (if j.val < 6 then 128 else 256))) else (if j.val < 10 then (if j.val < 8 then 512 else (if j.val < 9 then 1024 else 2048)) else (if j.val < 12 then (if j.val < 11 then 4096 else 8192) else (if j.val < 13 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 14 :=
  binaryCoordinateSpaceOfMasks 16 14
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 80).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 80).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 3 else (if j.val < 2 then 3 else 3)) else (if j.val < 5 then (if j.val < 4 then 5 else 1) else (if j.val < 6 then 1 else 5))) else (if j.val < 10 then (if j.val < 8 then 6 else (if j.val < 9 then 6 else 6)) else (if j.val < 12 then (if j.val < 11 then 4 else 7) else (if j.val < 13 then 3 else 5))))

private def generatorRows (j : Fin 14) :
    Array (Fin 6) :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then #[0,1,1] else (if j.val < 2 then #[0,0,1] else #[0,0,1])) else (if j.val < 5 then (if j.val < 4 then #[0,0,0,1,1] else #[1]) else (if j.val < 6 then #[1] else #[0,0,1,3,3]))) else (if j.val < 10 then (if j.val < 8 then #[0,0,0,0,1,3] else (if j.val < 9 then #[0,0,0,0,1,3] else #[0,0,0,0,1,3])) else (if j.val < 12 then (if j.val < 11 then #[0,0,1,3] else #[0,0,0,0,1,3,3]) else (if j.val < 13 then #[0,0,1] else #[0,0,0,0,1]))))

private def stateBasisRows (j : Fin 14) :
    Array (Fin 14) :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then #[5,6,7] else (if j.val < 2 then #[4,5,7] else #[1,4,6])) else (if j.val < 5 then (if j.val < 4 then #[0,1,5,6,7] else #[7]) else (if j.val < 6 then #[6] else #[4,7,6,6,7]))) else (if j.val < 10 then (if j.val < 8 then #[4,5,6,7,7,6] else (if j.val < 9 then #[4,6,7,8,6,6] else #[4,5,6,9,7,7])) else (if j.val < 12 then (if j.val < 11 then #[4,7,6,7] else #[4,5,6,7,7,6,7]) else (if j.val < 13 then #[4,13,6] else #[4,5,12,13,7]))))

private def termGenerator (j : Fin 14)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 14)
    (t : Fin (termCount j)) : Fin 14 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 14)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 80).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 80).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 80) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D80

namespace D81

private def displacementBasis (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 10 else 17)) else (if j.val < 5 then (if j.val < 4 then 34 else 65) else (if j.val < 6 then 130 else 259))) else (if j.val < 10 then (if j.val < 8 then 514 else (if j.val < 9 then 1027 else 2050)) else (if j.val < 12 then (if j.val < 11 then 4099 else 8194) else (if j.val < 13 then 16387 else 32770))))

private def displacementDual (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 8 else 16)) else (if j.val < 5 then (if j.val < 4 then 32 else 64) else (if j.val < 6 then 128 else 256))) else (if j.val < 10 then (if j.val < 8 then 512 else (if j.val < 9 then 1024 else 2048)) else (if j.val < 12 then (if j.val < 11 then 4096 else 8192) else (if j.val < 13 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 14 :=
  binaryCoordinateSpaceOfMasks 16 14
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 81).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 81).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 4 else 3)) else (if j.val < 5 then (if j.val < 4 then 4 else 2) else (if j.val < 6 then 1 else 5))) else (if j.val < 10 then (if j.val < 8 then 5 else (if j.val < 9 then 6 else 5)) else (if j.val < 12 then (if j.val < 11 then 4 else 6) else (if j.val < 13 then 3 else 4))))

private def generatorRows (j : Fin 14) :
    Array (Fin 6) :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0,0,1,1] else #[0,0,1])) else (if j.val < 5 then (if j.val < 4 then #[0,0,0,1] else #[1,1]) else (if j.val < 6 then #[1] else #[0,0,1,3,3]))) else (if j.val < 10 then (if j.val < 8 then #[0,0,0,1,3] else (if j.val < 9 then #[0,0,0,0,1,3] else #[0,0,0,1,3])) else (if j.val < 12 then (if j.val < 11 then #[0,0,1,3] else #[0,0,0,1,3,3]) else (if j.val < 13 then #[0,0,1] else #[0,0,0,1]))))

private def stateBasisRows (j : Fin 14) :
    Array (Fin 14) :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then #[5,6] else (if j.val < 2 then #[4,5,6,7] else #[1,4,7])) else (if j.val < 5 then (if j.val < 4 then #[0,1,5,6] else #[6,7]) else (if j.val < 6 then #[7] else #[5,7,6,6,7]))) else (if j.val < 10 then (if j.val < 8 then #[4,6,7,7,6] else (if j.val < 9 then #[5,6,7,8,6,6] else #[4,6,9,7,7])) else (if j.val < 12 then (if j.val < 11 then #[5,7,6,7] else #[4,6,7,7,6,7]) else (if j.val < 13 then #[5,13,6] else #[4,12,13,7]))))

private def termGenerator (j : Fin 14)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 14)
    (t : Fin (termCount j)) : Fin 14 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 14)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 81).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 81).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 81) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D81

namespace D82

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 82).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 82).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 16) : ℕ :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 2) else (if j.val < 3 then 3 else 5)) else (if j.val < 6 then (if j.val < 5 then 6 else 6) else (if j.val < 7 then 2 else 1))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 3 else 3) else (if j.val < 11 then 4 else 3)) else (if j.val < 14 then (if j.val < 13 then 2 else 4) else (if j.val < 15 then 1 else 2))))

private def generatorRows (j : Fin 16) :
    Array (Fin 6) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,1] else #[0,1]) else (if j.val < 3 then #[0,0,1] else #[0,0,0,1,1])) else (if j.val < 6 then (if j.val < 5 then #[0,0,0,0,1,1] else #[0,0,0,0,0,1]) else (if j.val < 7 then #[0,0] else #[0]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[0,3,3] else #[0,0,3]) else (if j.val < 11 then #[0,0,0,3] else #[0,0,3])) else (if j.val < 14 then (if j.val < 13 then #[0,3] else #[0,0,3,3]) else (if j.val < 15 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 16) :
    Array (Fin 16) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[6,7,0] else #[6,1]) else (if j.val < 3 then #[1,6,1] else #[0,1,7,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1,3,7,0,1] else #[0,2,3,6,7,0]) else (if j.val < 7 then #[6,7] else #[6]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[9,8,9] else #[8,9,8]) else (if j.val < 11 then #[8,9,10,8] else #[8,11,9])) else (if j.val < 14 then (if j.val < 13 then #[9,9] else #[8,9,8,9]) else (if j.val < 15 then #[15] else #[14,15]))))

private def termGenerator (j : Fin 16)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 16)
    (t : Fin (termCount j)) : Fin 16 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 16)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 82).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 82).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 82) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D82

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistry

end
