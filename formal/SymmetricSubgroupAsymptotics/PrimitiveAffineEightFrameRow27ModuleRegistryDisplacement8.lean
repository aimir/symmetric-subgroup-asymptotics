import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 8–10. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ModuleRegistry

local instance sourceGroupDisplacement8 : Group Source := PrimitiveAffineEightFrameRow27TopCertificate.group
local instance sourceInhabitedDisplacement8 : Inhabited Source := ⟨1⟩

namespace D8

private def displacementBasis (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 54 else 85) else (if j.val < 3 then 156 else (if j.val < 4 then 267 else 537))) else (if j.val < 8 then (if j.val < 6 then 1038 else (if j.val < 7 then 2067 else 4122)) else (if j.val < 9 then 8205 else (if j.val < 10 then 16415 else 32775))))

private def displacementDual (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 32 else 64) else (if j.val < 3 then 128 else (if j.val < 4 then 256 else 512))) else (if j.val < 8 then (if j.val < 6 then 1024 else (if j.val < 7 then 2048 else 4096)) else (if j.val < 9 then 8192 else (if j.val < 10 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 11 :=
  binaryCoordinateSpaceOfMasks 16 11
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 8).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 8).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 5 else 2) else (if j.val < 3 then 2 else (if j.val < 4 then 6 else 8))) else (if j.val < 8 then (if j.val < 6 then 6 else (if j.val < 7 then 7 else 9)) else (if j.val < 9 then 8 else (if j.val < 10 then 3 else 7))))

private def generatorRows (j : Fin 11) :
    Array (Fin 3) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0,0,0,0] else #[0,0]) else (if j.val < 3 then #[0,0] else (if j.val < 4 then #[0,0,0,0,0,0] else #[0,0,0,0,0,0,0,0]))) else (if j.val < 8 then (if j.val < 6 then #[0,0,0,0,0,0] else (if j.val < 7 then #[0,0,0,0,0,0,0] else #[0,0,0,0,0,0,0,0,0])) else (if j.val < 9 then #[0,0,0,0,0,0,0,0] else (if j.val < 10 then #[0,0,1] else #[0,0,0,0,0,1,1]))))

private def stateBasisRows (j : Fin 11) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,2,4,6,8] else #[5,7]) else (if j.val < 3 then #[2,4] else (if j.val < 4 then #[0,2,3,4,6,8] else #[0,1,2,3,5,6,7,8]))) else (if j.val < 8 then (if j.val < 6 then #[0,2,4,6,7,8] else (if j.val < 7 then #[1,2,3,4,5,6,7] else #[0,1,2,3,4,5,6,7,8])) else (if j.val < 9 then #[1,2,3,4,5,6,7,8] else (if j.val < 10 then #[2,4,10] else #[0,5,6,7,8,9,10]))))

private def termGenerator (j : Fin 11)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 11)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 11)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 8).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 8).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow27ModuleRepresentation.representation PrimitiveAffineEightFrameRow27TopCertificate.ambient
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 8) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D8

namespace D9

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
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 9).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 9).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 5 else 6)) else (if j.val < 5 then (if j.val < 4 then 6 else 3) else (if j.val < 6 then 3 else 2))) else (if j.val < 10 then (if j.val < 8 then 2 else (if j.val < 9 then 4 else 4)) else (if j.val < 12 then (if j.val < 11 then 1 else 1) else (if j.val < 13 then 11 else 7))))

private def generatorRows (j : Fin 14) :
    Array (Fin 3) :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then #[0,0,0,0,0] else (if j.val < 2 then #[0,0,0,0,0] else #[0,0,0,0,0,0])) else (if j.val < 5 then (if j.val < 4 then #[0,0,0,0,0,0] else #[0,0,0]) else (if j.val < 6 then #[0,0,0] else #[0,0]))) else (if j.val < 10 then (if j.val < 8 then #[0,0] else (if j.val < 9 then #[0,0,0,0] else #[0,0,0,0])) else (if j.val < 12 then (if j.val < 11 then #[0] else #[0]) else (if j.val < 13 then #[0,0,0,0,0,0,0,0,0,0,1] else #[0,0,0,0,0,1,1]))))

private def stateBasisRows (j : Fin 14) :
    Array (Fin 14) :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then #[2,4,6,8,10] else (if j.val < 2 then #[3,5,7,9,11] else #[0,2,4,6,8,10])) else (if j.val < 5 then (if j.val < 4 then #[1,3,5,7,9,11] else #[2,8,10]) else (if j.val < 6 then #[3,9,11] else #[0,6]))) else (if j.val < 10 then (if j.val < 8 then #[1,7] else (if j.val < 9 then #[0,4,6,8] else #[1,5,7,9])) else (if j.val < 12 then (if j.val < 11 then #[2] else #[3]) else (if j.val < 13 then #[2,3,4,5,6,7,8,9,10,11,13] else #[2,4,6,8,10,12,13]))))

private def termGenerator (j : Fin 14)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 14)
    (t : Fin (termCount j)) : Fin 14 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 14)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 9).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 9).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow27ModuleRepresentation.representation PrimitiveAffineEightFrameRow27TopCertificate.ambient
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 9) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D9

namespace D10

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
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 10).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 10).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 16) : ℕ :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 2 else 4)) else (if j.val < 6 then (if j.val < 5 then 4 else 4) else (if j.val < 7 then 4 else 6))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 3 else 5) else (if j.val < 11 then 5 else 7)) else (if j.val < 14 then (if j.val < 13 then 5 else 5) else (if j.val < 15 then 1 else 2))))

private def generatorRows (j : Fin 16) :
    Array (Fin 3) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,1] else #[0,1,1]) else (if j.val < 3 then #[0,1] else #[0,0,1,1])) else (if j.val < 6 then (if j.val < 5 then #[0,0,0,1] else #[0,0,1,1]) else (if j.val < 7 then #[0,0,0,1] else #[0,0,0,0,1,1]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[0,0,1] else #[0,0,0,1,1]) else (if j.val < 11 then #[0,0,0,0,1] else #[0,0,0,0,0,1,1])) else (if j.val < 14 then (if j.val < 13 then #[0,0,0,0,1] else #[0,0,0,1,1]) else (if j.val < 15 then #[1] else #[1,1]))))

private def stateBasisRows (j : Fin 16) :
    Array (Fin 16) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[2,3,1] else #[2,0,1]) else (if j.val < 3 then #[3,1] else #[2,3,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,2,3,1] else #[1,2,0,1]) else (if j.val < 7 then #[3,6,8,1] else #[2,3,7,9,0,1]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[3,8,1] else #[2,3,9,0,1]) else (if j.val < 11 then #[3,6,8,10,1] else #[2,3,7,9,11,0,1])) else (if j.val < 14 then (if j.val < 13 then #[0,2,3,4,1] else #[1,2,5,0,1]) else (if j.val < 15 then #[15] else #[14,15]))))

private def termGenerator (j : Fin 16)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 16)
    (t : Fin (termCount j)) : Fin 16 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 16)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 10).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 10).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow27ModuleRepresentation.representation PrimitiveAffineEightFrameRow27TopCertificate.ambient
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 10) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D10

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ModuleRegistry

end
