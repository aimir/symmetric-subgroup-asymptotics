import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 40–42. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleRegistry

local instance sourceGroupDisplacement40 : Group Source := PrimitiveAffineEightFrameRow8TopCertificate.group
local instance sourceInhabitedDisplacement40 : Inhabited Source := ⟨1⟩

namespace D40

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 27 else (if j.val < 2 then 45 else 78)) else (if j.val < 4 then 135 else (if j.val < 5 then 257 else 514))) else (if j.val < 9 then (if j.val < 7 then 1028 else (if j.val < 8 then 2056 else 4107)) else (if j.val < 10 then 8205 else (if j.val < 11 then 16398 else 32775))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 16 else (if j.val < 2 then 32 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 40).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 40).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 3)) else (if j.val < 4 then 2 else (if j.val < 5 then 3 else 5))) else (if j.val < 9 then (if j.val < 7 then 6 else (if j.val < 8 then 4 else 4)) else (if j.val < 10 then 3 else (if j.val < 11 then 3 else 2))))

private def generatorRows (j : Fin 12) :
    Array (Fin 5) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[1] else #[0,0,1])) else (if j.val < 4 then #[0,1] else (if j.val < 5 then #[0,0,1] else #[0,0,1,1,2]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,0,1,1,2] else (if j.val < 8 then #[0,0,0,1] else #[0,1,1,2])) else (if j.val < 10 then #[1,1,2] else (if j.val < 11 then #[0,0,1] else #[0,1]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 13) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[1,0] else (if j.val < 2 then #[0] else #[1,3,3])) else (if j.val < 4 then #[1,3] else (if j.val < 5 then #[1,9,5] else #[1,9,5,6,5]))) else (if j.val < 9 then (if j.val < 7 then #[1,6,9,5,6,5] else (if j.val < 8 then #[1,5,9,5] else #[9,0,5,5])) else (if j.val < 10 then #[0,5,5] else (if j.val < 11 then #[1,11,11] else #[1,11]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 13 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 40).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 40).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow8ModuleRepresentation.representation PrimitiveAffineEightFrameRow8TopCertificate.ambient
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 40) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D40

namespace D41

private def displacementBasis (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 15 else (if j.val < 2 then 20 else 34)) else (if j.val < 4 then 65 else (if j.val < 5 then 135 else 257))) else (if j.val < 9 then (if j.val < 7 then 514 else (if j.val < 8 then 1028 else 2055)) else (if j.val < 11 then (if j.val < 10 then 4100 else 8194) else (if j.val < 12 then 16385 else 32775))))

private def displacementDual (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 8 else (if j.val < 2 then 16 else 32)) else (if j.val < 4 then 64 else (if j.val < 5 then 128 else 256))) else (if j.val < 9 then (if j.val < 7 then 512 else (if j.val < 8 then 1024 else 2048)) else (if j.val < 11 then (if j.val < 10 then 4096 else 8192) else (if j.val < 12 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 13 :=
  binaryCoordinateSpaceOfMasks 16 13
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 41).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 41).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 2)) else (if j.val < 4 then 3 else (if j.val < 5 then 3 else 3))) else (if j.val < 9 then (if j.val < 7 then 5 else (if j.val < 8 then 6 else 5)) else (if j.val < 11 then (if j.val < 10 then 6 else 4) else (if j.val < 12 then 3 else 3))))

private def generatorRows (j : Fin 13) :
    Array (Fin 5) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,1] else #[0,1])) else (if j.val < 4 then #[0,0,1] else (if j.val < 5 then #[0,0,1] else #[0,0,1]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,1,1,2] else (if j.val < 8 then #[0,0,0,1,1,2] else #[0,0,0,0,1])) else (if j.val < 11 then (if j.val < 10 then #[0,0,0,1,1,2] else #[0,1,1,2]) else (if j.val < 12 then #[0,0,1] else #[0,0,1]))))

private def stateBasisRows (j : Fin 13) :
    Array (Fin 14) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,1] else #[2,1])) else (if j.val < 4 then #[2,4,4] else (if j.val < 5 then #[0,2,4] else #[2,10,6]))) else (if j.val < 9 then (if j.val < 7 then #[2,10,6,7,6] else (if j.val < 8 then #[2,7,10,6,7,6] else #[0,2,6,10,6])) else (if j.val < 11 then (if j.val < 10 then #[0,2,10,1,6,6] else #[2,1,6,6]) else (if j.val < 12 then #[2,12,12] else #[0,2,12]))))

private def termGenerator (j : Fin 13)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 13)
    (t : Fin (termCount j)) : Fin 14 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 13)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 41).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 41).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow8ModuleRepresentation.representation PrimitiveAffineEightFrameRow8TopCertificate.ambient
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 41) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D41

namespace D42

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
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 42).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 42).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 16) : ℕ :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 4) else (if j.val < 3 then 5 else 3)) else (if j.val < 6 then (if j.val < 5 then 3 else 2) else (if j.val < 7 then 2 else 1))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 2 else 4) else (if j.val < 11 then 5 else 3)) else (if j.val < 14 then (if j.val < 13 then 3 else 2) else (if j.val < 15 then 2 else 1))))

private def generatorRows (j : Fin 16) :
    Array (Fin 5) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0,1,1,2]) else (if j.val < 3 then #[0,0,1,1,2] else #[0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1,2] else #[1,2]) else (if j.val < 7 then #[0,1] else #[1]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[0,1] else #[0,1,1,2]) else (if j.val < 11 then #[0,0,1,1,2] else #[0,0,1])) else (if j.val < 14 then (if j.val < 13 then #[0,1,2] else #[1,2]) else (if j.val < 15 then #[0,1] else #[1]))))

private def stateBasisRows (j : Fin 16) :
    Array (Fin 16) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[4,0] else #[4,0,1,0]) else (if j.val < 3 then #[1,4,0,1,0] else #[0,4,0])) else (if j.val < 6 then (if j.val < 5 then #[4,0,0] else #[0,0]) else (if j.val < 7 then #[6,6] else #[6]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[12,8] else #[12,8,9,8]) else (if j.val < 11 then #[9,12,8,9,8] else #[8,12,8])) else (if j.val < 14 then (if j.val < 13 then #[12,8,8] else #[8,8]) else (if j.val < 15 then #[14,14] else #[14]))))

private def termGenerator (j : Fin 16)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 16)
    (t : Fin (termCount j)) : Fin 16 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 16)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 42).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow8ModuleRepresentation.charts 42).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow8ModuleRepresentation.representation PrimitiveAffineEightFrameRow8TopCertificate.ambient
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states 42) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D42

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleRegistry

end
