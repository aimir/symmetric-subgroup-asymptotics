import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 32–47. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleRegistry

local instance sourceGroupDisplacement32 : Group Source := PrimitiveAffineEightFrameRow20TopCertificate.group
local instance sourceInhabitedDisplacement32 : Inhabited Source := ⟨1⟩

namespace D32

private def displacementBasis (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 255 else 317) else (if j.val < 3 then 540 else 1080)) else (if j.val < 6 then (if j.val < 5 then 2115 else 4211) else (if j.val < 7 then 8241 else (if j.val < 8 then 16419 else 32827))))

private def displacementDual (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 128 else 256) else (if j.val < 3 then 512 else 1024)) else (if j.val < 6 then (if j.val < 5 then 2048 else 4096) else (if j.val < 7 then 8192 else (if j.val < 8 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 9 :=
  binaryCoordinateSpaceOfMasks 16 9
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 32).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 32).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 5 else 6) else (if j.val < 3 then 3 else 4)) else (if j.val < 6 then (if j.val < 5 then 4 else 3) else (if j.val < 7 then 5 else (if j.val < 8 then 5 else 1))))

private def generatorRows (j : Fin 9) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,1,1,2] else #[0,0,0,1,1,2]) else (if j.val < 3 then #[1,1,1] else #[0,0,1,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1,1,1] else #[0,1,1]) else (if j.val < 7 then #[0,0,0,1,2] else (if j.val < 8 then #[0,0,1,1,2] else #[1]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 9) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,5,1,5,2] else #[1,5,6,1,2,2]) else (if j.val < 3 then #[1,2,6] else #[1,6,2,5])) else (if j.val < 6 then (if j.val < 5 then #[2,1,2,6] else #[6,5,6]) else (if j.val < 7 then #[1,5,6,1,2] else (if j.val < 8 then #[1,6,1,6,2] else #[5]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 32).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 32).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 32) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D32

namespace D33

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
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 33).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 33).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 4 else 4) else (if j.val < 3 then 4 else (if j.val < 4 then 3 else 4))) else (if j.val < 7 then (if j.val < 6 then 3 else 4) else (if j.val < 8 then 6 else (if j.val < 9 then 3 else 5))))

private def generatorRows (j : Fin 10) :
    Array (Fin 3) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1,1,1,2] else #[1,1,2,2]) else (if j.val < 3 then #[1,1,1,2] else (if j.val < 4 then #[1,1,2] else #[0,1,1,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,1,1] else #[1,1,1,2]) else (if j.val < 8 then #[1,1,1,1,2,2] else (if j.val < 9 then #[1,1,2] else #[1,1,1,1,2]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1,2,1] else #[0,3,0,1]) else (if j.val < 3 then #[0,2,3,0] else (if j.val < 4 then #[1,2,1] else #[6,0,2,3]))) else (if j.val < 7 then (if j.val < 6 then #[7,1,2] else #[0,2,7,1]) else (if j.val < 8 then #[1,3,6,7,0,1] else (if j.val < 9 then #[1,7,0] else #[0,1,6,7,1]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 33).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 33).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 33) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D33

namespace D34

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 1285 else 2570)) else (if j.val < 6 then (if j.val < 5 then 4382 else 8743) else (if j.val < 7 then 16667 else 33325)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 34).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 34).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 2) else (if j.val < 3 then 3 else 4)) else (if j.val < 6 then (if j.val < 5 then 4 else 4) else (if j.val < 7 then 4 else 4)))

private def generatorRows (j : Fin 8) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1] else #[0,1]) else (if j.val < 3 then #[0,0,1] else #[0,0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1,1,1] else #[0,1,1,1]) else (if j.val < 7 then #[0,0,1,1] else #[0,1,1,1])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[6,0,1] else #[7,0]) else (if j.val < 3 then #[2,7,0] else #[3,6,7,1])) else (if j.val < 6 then (if j.val < 5 then #[6,0,1,3] else #[7,0,2,3]) else (if j.val < 7 then #[6,7,0,3] else #[6,1,2,3])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 34).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 34).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 34) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D34

namespace D35

private def displacementBasis (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 306) else (if j.val < 3 then 534 else 1181)) else (if j.val < 6 then (if j.val < 5 then 2076 else 4227) else (if j.val < 7 then 8337 else (if j.val < 8 then 16428 else 32817))))

private def displacementDual (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 256) else (if j.val < 3 then 512 else 1024)) else (if j.val < 6 then (if j.val < 5 then 2048 else 4096) else (if j.val < 7 then 8192 else (if j.val < 8 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 9 :=
  binaryCoordinateSpaceOfMasks 16 9
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 35).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 35).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 7 else 5) else (if j.val < 3 then 4 else 3)) else (if j.val < 6 then (if j.val < 5 then 4 else 5) else (if j.val < 7 then 1 else (if j.val < 8 then 6 else 7))))

private def generatorRows (j : Fin 9) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,1,1,1,1,2] else #[0,0,1,1,2]) else (if j.val < 3 then #[0,0,1,2] else #[0,1,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1,1,1] else #[0,0,1,1,2]) else (if j.val < 7 then #[1] else (if j.val < 8 then #[0,0,0,1,1,2] else #[0,0,0,1,1,1,2]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[2,3,2,3,6,7,2] else #[2,3,2,7,2]) else (if j.val < 3 then #[2,3,6,2] else #[2,3,6])) else (if j.val < 6 then (if j.val < 5 then #[3,2,3,7] else #[2,3,2,3,2]) else (if j.val < 7 then #[6] else (if j.val < 8 then #[2,3,6,2,3,2] else #[2,3,7,2,3,7,2]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 35).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 35).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 35) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D35

namespace D36

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 311 else (if j.val < 4 then 537 else 1074))) else (if j.val < 7 then (if j.val < 6 then 2067 else 4140) else (if j.val < 8 then 8244 else (if j.val < 9 then 16425 else 32830))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 36).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 36).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 5 else 7) else (if j.val < 3 then 7 else (if j.val < 4 then 5 else 4))) else (if j.val < 7 then (if j.val < 6 then 5 else 2) else (if j.val < 8 then 1 else (if j.val < 9 then 6 else 8))))

private def generatorRows (j : Fin 10) :
    Array (Fin 3) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0,1,1,2] else #[0,0,0,1,1,2,2]) else (if j.val < 3 then #[0,0,0,1,1,2,2] else (if j.val < 4 then #[0,0,0,1,2] else #[0,1,1,2]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,1,2,2] else #[1,1]) else (if j.val < 8 then #[1] else (if j.val < 9 then #[0,0,1,1,2,2] else #[0,0,0,0,1,1,1,2]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[2,7,2,6,3] else #[3,6,7,3,7,2,3]) else (if j.val < 3 then #[3,6,7,6,7,2,3] else (if j.val < 4 then #[2,3,6,6,2] else #[7,2,3,3]))) else (if j.val < 7 then (if j.val < 6 then #[6,7,2,2,3] else #[6,7]) else (if j.val < 8 then #[6] else (if j.val < 9 then #[3,7,3,6,2,3] else #[2,3,6,7,2,3,7,2]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 36).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 36).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 36) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D36

namespace D37

private def displacementBasis (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 170 else 312) else (if j.val < 3 then 531 else 1128)) else (if j.val < 6 then (if j.val < 5 then 2124 else 4131) else (if j.val < 7 then 8299 else (if j.val < 8 then 16422 else 32820))))

private def displacementDual (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 128 else 256) else (if j.val < 3 then 512 else 1024)) else (if j.val < 6 then (if j.val < 5 then 2048 else 4096) else (if j.val < 7 then 8192 else (if j.val < 8 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 9 :=
  binaryCoordinateSpaceOfMasks 16 9
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 37).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 37).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 8 else 2) else (if j.val < 3 then 5 else 5)) else (if j.val < 6 then (if j.val < 5 then 4 else 6) else (if j.val < 7 then 1 else (if j.val < 8 then 3 else 6))))

private def generatorRows (j : Fin 9) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,0,1,1,1,1,2] else #[1,1]) else (if j.val < 3 then #[0,0,0,1,2] else #[0,0,1,1,2])) else (if j.val < 6 then (if j.val < 5 then #[0,0,1,2] else #[0,0,0,1,1,2]) else (if j.val < 7 then #[1] else (if j.val < 8 then #[0,1,1] else #[0,0,1,1,1,2]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[2,3,7,2,3,6,7,2] else #[3,6]) else (if j.val < 3 then #[2,3,7,6,2] else #[3,7,2,7,2])) else (if j.val < 6 then (if j.val < 5 then #[2,7,6,2] else #[2,3,7,2,3,2]) else (if j.val < 7 then #[6] else (if j.val < 8 then #[6,6,7] else #[2,3,2,3,7,2]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 37).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 37).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 37) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D37

namespace D38

private def displacementBasis (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 255 else 317) else (if j.val < 3 then 540 else 1080)) else (if j.val < 6 then (if j.val < 5 then 2115 else 4211) else (if j.val < 7 then 8241 else (if j.val < 8 then 16419 else 32827))))

private def displacementDual (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 128 else 256) else (if j.val < 3 then 512 else 1024)) else (if j.val < 6 then (if j.val < 5 then 2048 else 4096) else (if j.val < 7 then 8192 else (if j.val < 8 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 9 :=
  binaryCoordinateSpaceOfMasks 16 9
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 38).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 38).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 6 else 6) else (if j.val < 3 then 3 else 3)) else (if j.val < 6 then (if j.val < 5 then 4 else 2) else (if j.val < 7 then 5 else (if j.val < 8 then 5 else 2))))

private def generatorRows (j : Fin 9) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,0,1,1,2] else #[0,0,0,1,1,2]) else (if j.val < 3 then #[1,1,1] else #[0,1,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1,1,1] else #[1,1]) else (if j.val < 7 then #[0,0,0,1,2] else (if j.val < 8 then #[0,0,1,1,2] else #[0,1]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[2,6,7,2,6,3] else #[2,6,7,2,3,3]) else (if j.val < 3 then #[2,3,7] else #[2,3,6])) else (if j.val < 6 then (if j.val < 5 then #[3,2,3,7] else #[6,7]) else (if j.val < 7 then #[2,6,7,2,3] else (if j.val < 8 then #[2,7,2,7,3] else #[7,6]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 38).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 38).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 38) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D38

namespace D39

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
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 39).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 39).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 4 else (if j.val < 4 then 4 else 5))) else (if j.val < 7 then (if j.val < 6 then 3 else 3) else (if j.val < 8 then 6 else (if j.val < 9 then 3 else 5))))

private def generatorRows (j : Fin 10) :
    Array (Fin 3) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1,2] else #[0,1,1]) else (if j.val < 3 then #[1,1,1,2] else (if j.val < 4 then #[0,1,1,2] else #[0,0,1,1,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,1,1] else #[0,1,2]) else (if j.val < 8 then #[0,1,1,1,1,1] else (if j.val < 9 then #[1,1,2] else #[0,1,1,1,2]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[7,1,0] else #[7,2,3]) else (if j.val < 3 then #[0,2,3,0] else (if j.val < 4 then #[7,0,1,0] else #[4,7,0,2,3]))) else (if j.val < 7 then (if j.val < 6 then #[8,1,2] else #[7,8,0]) else (if j.val < 8 then #[7,0,2,3,4,8] else (if j.val < 9 then #[1,8,0] else #[7,2,4,8,0]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 39).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 39).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 39) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D39

namespace D40

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
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 40).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 40).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 4 else 4) else (if j.val < 3 then 4 else (if j.val < 4 then 3 else 4))) else (if j.val < 7 then (if j.val < 6 then 4 else 4) else (if j.val < 8 then 6 else (if j.val < 9 then 5 else 3))))

private def generatorRows (j : Fin 10) :
    Array (Fin 3) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1,1,1,2] else #[0,1,1,2]) else (if j.val < 3 then #[0,1,1,1] else (if j.val < 4 then #[1,1,2] else #[0,1,1,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,1,1] else #[1,1,1,2]) else (if j.val < 8 then #[0,1,1,1,1,2] else (if j.val < 9 then #[0,1,1,1,1] else #[1,1,2]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1,2,1] else #[8,0,1,1]) else (if j.val < 3 then #[8,0,1,2] else (if j.val < 4 then #[1,2,1] else #[7,0,2,3]))) else (if j.val < 7 then (if j.val < 6 then #[4,8,1,2] else #[1,2,4,1]) else (if j.val < 8 then #[8,0,1,4,7,1] else (if j.val < 9 then #[8,0,1,3,4] else #[4,7,1]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 40).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 40).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 40) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D40

namespace D41

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
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 41).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 41).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 3 else 5) else (if j.val < 3 then 4 else (if j.val < 4 then 4 else 4))) else (if j.val < 7 then (if j.val < 6 then 4 else 7) else (if j.val < 8 then 5 else (if j.val < 9 then 5 else 6))))

private def generatorRows (j : Fin 10) :
    Array (Fin 3) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0,1] else #[0,0,1,1,2]) else (if j.val < 3 then #[1,1,1,2] else (if j.val < 4 then #[0,0,1,1] else #[0,1,1,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,1,1] else #[0,0,1,1,1,1,1]) else (if j.val < 8 then #[0,0,1,1,2] else (if j.val < 9 then #[1,1,1,1,2] else #[0,0,1,1,1,1]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[7,8,3] else #[7,8,1,2,0]) else (if j.val < 3 then #[0,2,3,0] else (if j.val < 4 then #[7,8,0,3] else #[7,0,2,3]))) else (if j.val < 7 then (if j.val < 6 then #[4,8,1,2] else #[7,8,0,1,3,4,7]) else (if j.val < 8 then #[7,8,2,4,0] else (if j.val < 9 then #[0,1,4,7,0] else #[7,8,0,2,3,4]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 41).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 41).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 41) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D41

namespace D42

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
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 42).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 42).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 4 else (if j.val < 4 then 4 else 5))) else (if j.val < 7 then (if j.val < 6 then 4 else 5) else (if j.val < 8 then 6 else (if j.val < 9 then 5 else 7))))

private def generatorRows (j : Fin 10) :
    Array (Fin 3) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0,1] else #[0,1,1]) else (if j.val < 3 then #[0,1,1,1] else (if j.val < 4 then #[0,0,1,1] else #[0,0,1,1,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,1,1] else #[0,0,1,1,1]) else (if j.val < 8 then #[0,1,1,1,1,1] else (if j.val < 9 then #[0,1,1,1,1] else #[0,0,1,1,1,1,1]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[8,9,3] else #[8,2,3]) else (if j.val < 3 then #[9,0,1,2] else (if j.val < 4 then #[8,9,0,3] else #[4,8,0,2,3]))) else (if j.val < 7 then (if j.val < 6 then #[5,9,1,2] else #[8,9,0,3,5]) else (if j.val < 8 then #[8,1,2,3,4,5] else (if j.val < 9 then #[9,0,1,3,5] else #[8,9,0,2,3,4,5]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 42).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 42).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 42) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D42

namespace D43

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
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 43).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 43).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 3 else (if j.val < 2 then 6 else 3)) else (if j.val < 4 then 4 else (if j.val < 5 then 8 else 6))) else (if j.val < 9 then (if j.val < 7 then 8 else (if j.val < 8 then 7 else 6)) else (if j.val < 10 then 4 else (if j.val < 11 then 6 else 5))))

private def generatorRows (j : Fin 12) :
    Array (Fin 3) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,1,2] else (if j.val < 2 then #[0,0,1,1,2,2] else #[0,1,2])) else (if j.val < 4 then #[0,1,1,2] else (if j.val < 5 then #[0,0,1,1,1,1,2,2] else #[0,1,1,1,1,2]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,0,1,1,1,2,2] else (if j.val < 8 then #[0,0,1,1,1,1,2] else #[0,1,1,1,1,2])) else (if j.val < 10 then #[0,1,1,2] else (if j.val < 11 then #[0,0,1,1,1,2] else #[0,1,1,2,2]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 12) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[9,1,1] else (if j.val < 2 then #[8,9,0,1,0,1] else #[8,1,0])) else (if j.val < 4 then #[9,0,1,1] else (if j.val < 5 then #[8,9,0,1,5,8,0,1] else #[8,0,4,5,9,0]))) else (if j.val < 9 then (if j.val < 7 then #[4,8,9,0,5,8,0,1] else (if j.val < 8 then #[5,8,1,4,5,9,0] else #[8,0,1,8,9,0])) else (if j.val < 10 then #[9,0,8,1] else (if j.val < 11 then #[8,9,0,8,9,1] else #[8,1,8,0,1]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 43).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 43).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 43) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D43

namespace D44

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
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 44).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 44).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 3 else 3)) else (if j.val < 4 then 5 else (if j.val < 5 then 3 else 7))) else (if j.val < 9 then (if j.val < 7 then 4 else (if j.val < 8 then 9 else 4)) else (if j.val < 10 then 6 else (if j.val < 11 then 5 else 2))))

private def generatorRows (j : Fin 12) :
    Array (Fin 3) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0,1,2] else (if j.val < 2 then #[0,1,1] else #[0,1,2])) else (if j.val < 4 then #[0,0,1,1,2] else (if j.val < 5 then #[0,1,1] else #[0,1,1,1,1,1,2]))) else (if j.val < 9 then (if j.val < 7 then #[0,1,1,1] else (if j.val < 8 then #[0,0,0,1,1,1,1,1,2] else #[0,1,1,2])) else (if j.val < 10 then #[0,0,1,1,1,2] else (if j.val < 11 then #[0,1,1,1,2] else #[0,1]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 13) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[2,9,1,0] else (if j.val < 2 then #[2,0,1] else #[9,1,0])) else (if j.val < 4 then #[2,9,0,1,0] else (if j.val < 5 then #[2,0,6] else #[9,0,2,5,6,10,0]))) else (if j.val < 9 then (if j.val < 7 then #[5,0,1,6] else (if j.val < 8 then #[2,6,9,1,2,5,6,10,0] else #[9,0,10,0])) else (if j.val < 10 then #[2,9,0,1,2,0] else (if j.val < 11 then #[2,0,1,10,0] else #[10,2]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 13 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 44).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 44).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 44) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D44

namespace D45

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
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 45).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 45).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 4 else 2)) else (if j.val < 4 then 5 else (if j.val < 5 then 7 else 4))) else (if j.val < 9 then (if j.val < 7 then 8 else (if j.val < 8 then 5 else 2)) else (if j.val < 10 then 6 else (if j.val < 11 then 5 else 5))))

private def generatorRows (j : Fin 12) :
    Array (Fin 3) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0,1,2] else (if j.val < 2 then #[0,1,1,2] else #[0,1])) else (if j.val < 4 then #[0,0,1,1,2] else (if j.val < 5 then #[0,1,1,1,1,1,2] else #[0,1,1,1]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,0,1,1,1,1,2] else (if j.val < 8 then #[0,0,1,1,1] else #[0,1])) else (if j.val < 10 then #[0,0,1,1,1,2] else (if j.val < 11 then #[0,0,1,1,2] else #[0,1,1,1,2]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 13) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[2,10,1,1] else (if j.val < 2 then #[10,0,1,1] else #[2,1])) else (if j.val < 4 then #[2,10,0,1,1] else (if j.val < 5 then #[10,0,1,2,6,9,1] else #[2,1,5,6]))) else (if j.val < 9 then (if j.val < 7 then #[2,5,10,0,2,6,9,1] else (if j.val < 8 then #[2,6,0,5,6] else #[2,9])) else (if j.val < 10 then #[2,10,0,2,9,1] else (if j.val < 11 then #[9,10,1,9,1] else #[2,1,2,9,1]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 13 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 45).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 45).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 45) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D45

namespace D46

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
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 46).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 46).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 4 else 4)) else (if j.val < 4 then 3 else (if j.val < 5 then 7 else 7))) else (if j.val < 9 then (if j.val < 7 then 8 else (if j.val < 8 then 10 else 5)) else (if j.val < 10 then 4 else (if j.val < 11 then 2 else 7))))

private def generatorRows (j : Fin 12) :
    Array (Fin 3) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0,1,1,2] else #[0,0,1,2])) else (if j.val < 4 then #[0,1,1] else (if j.val < 5 then #[0,1,1,1,1,1,2] else #[0,0,1,1,1,1,2]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,0,1,1,1,1,2] else (if j.val < 8 then #[0,0,0,1,1,1,1,1,1,2] else #[0,0,1,1,2])) else (if j.val < 10 then #[0,1,1,1] else (if j.val < 11 then #[0,1] else #[0,0,0,1,1,1,2]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 13) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[2,1] else (if j.val < 2 then #[9,0,1,0] else #[2,9,1,0])) else (if j.val < 4 then #[2,0,1] else (if j.val < 5 then #[9,0,1,2,6,9,0] else #[2,9,2,5,6,9,0]))) else (if j.val < 9 then (if j.val < 7 then #[2,5,9,0,2,6,9,0] else (if j.val < 8 then #[2,6,9,0,1,2,5,6,9,0] else #[2,9,1,2,0])) else (if j.val < 10 then #[2,0,2,9] else (if j.val < 11 then #[9,2] else #[2,9,10,1,2,9,0]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 13 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 46).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 46).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 46) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D46

namespace D47

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
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 47).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 47).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 3 else (if j.val < 2 then 3 else 2)) else (if j.val < 4 then 4 else (if j.val < 5 then 3 else 4))) else (if j.val < 9 then (if j.val < 7 then 5 else (if j.val < 8 then 6 else 4)) else (if j.val < 10 then 5 else (if j.val < 11 then 4 else 3))))

private def generatorRows (j : Fin 12) :
    Array (Fin 3) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0,1] else (if j.val < 2 then #[0,1,1] else #[0,1])) else (if j.val < 4 then #[0,0,1,1] else (if j.val < 5 then #[0,1,1] else #[0,1,1,1]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,1,1,1] else (if j.val < 8 then #[0,0,0,1,1,1] else #[0,1,1,1])) else (if j.val < 10 then #[0,0,1,1,1] else (if j.val < 11 then #[0,0,1,1] else #[0,0,1]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 14) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[2,3,1] else (if j.val < 2 then #[2,0,1] else #[3,1])) else (if j.val < 4 then #[2,3,0,1] else (if j.val < 5 then #[2,0,7] else #[3,1,6,7]))) else (if j.val < 9 then (if j.val < 7 then #[3,6,0,1,7] else (if j.val < 8 then #[2,3,7,0,6,7] else #[3,1,2,3])) else (if j.val < 10 then #[2,3,0,1,2] else (if j.val < 11 then #[2,10,2,3] else #[3,11,2]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 14 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 47).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 47).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 47) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D47

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleRegistry

end
