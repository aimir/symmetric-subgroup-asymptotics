import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 80–87. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

local instance sourceGroupDisplacement80 : Group Source := PrimitiveAffineEightFrameRow0TopCertificate.group
local instance sourceInhabitedDisplacement80 : Inhabited Source := ⟨1⟩

namespace D80

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 312 else (if j.val < 4 then 549 else 1085))) else (if j.val < 7 then (if j.val < 6 then 2095 else 4137) else (if j.val < 8 then 8199 else (if j.val < 9 then 16428 else 32781))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 80).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 80).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 4 else (if j.val < 4 then 3 else 4))) else (if j.val < 7 then (if j.val < 6 then 4 else 3) else (if j.val < 8 then 5 else (if j.val < 9 then 1 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,1,1] else (if j.val < 4 then #[0,0,1] else #[0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,0,1] else #[0,0,1]) else (if j.val < 8 then #[0,0,0,1,1] else (if j.val < 9 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[2] else #[1,2]) else (if j.val < 3 then #[2,4,3,4] else (if j.val < 4 then #[3,4,3] else #[3,4,5,3]))) else (if j.val < 7 then (if j.val < 6 then #[2,3,6,4] else #[2,4,4]) else (if j.val < 8 then #[2,3,4,3,4] else (if j.val < 9 then #[10] else #[9,10]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 80).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 80).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 80) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D80

namespace D81

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 294 else (if j.val < 4 then 540 else 1059))) else (if j.val < 7 then (if j.val < 6 then 2070 else 4151) else (if j.val < 8 then 8254 else (if j.val < 9 then 16434 else 32820))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 81).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 81).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else (if j.val < 4 then 4 else 5))) else (if j.val < 7 then (if j.val < 6 then 4 else 3) else (if j.val < 8 then 4 else (if j.val < 9 then 1 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,1,1] else (if j.val < 4 then #[0,0,0,1] else #[0,0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,0,1] else #[0,0,1]) else (if j.val < 8 then #[0,0,1,1] else (if j.val < 9 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[2] else #[1,2]) else (if j.val < 3 then #[4,3,4] else (if j.val < 4 then #[2,3,4,3] else #[2,3,4,5,3]))) else (if j.val < 7 then (if j.val < 6 then #[2,3,6,4] else #[2,4,4]) else (if j.val < 8 then #[3,4,3,4] else (if j.val < 9 then #[10] else #[9,10]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 81).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 81).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 81) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D81

namespace D82

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 257 else (if j.val < 4 then 514 else 1028))) else (if j.val < 7 then (if j.val < 6 then 2056 else 4112) else (if j.val < 8 then 8224 else (if j.val < 9 then 16405 else 32810))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 82).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 82).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else (if j.val < 4 then 3 else 4))) else (if j.val < 7 then (if j.val < 6 then 3 else 2) else (if j.val < 8 then 4 else (if j.val < 9 then 1 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,1,1] else (if j.val < 4 then #[0,0,1] else #[0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,1] else #[0,1]) else (if j.val < 8 then #[0,0,1,1] else (if j.val < 9 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[2] else #[1,2]) else (if j.val < 3 then #[4,3,4] else (if j.val < 4 then #[3,4,3] else #[3,4,5,3]))) else (if j.val < 7 then (if j.val < 6 then #[3,6,4] else #[4,4]) else (if j.val < 8 then #[3,4,3,4] else (if j.val < 9 then #[10] else #[9,10]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 82).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 82).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 82) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D82

namespace D83

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 294 else (if j.val < 4 then 540 else 1059))) else (if j.val < 7 then (if j.val < 6 then 2070 else 4151) else (if j.val < 8 then 8254 else (if j.val < 9 then 16434 else 32820))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 83).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 83).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 4 else (if j.val < 4 then 5 else 6))) else (if j.val < 7 then (if j.val < 6 then 4 else 3) else (if j.val < 8 then 5 else (if j.val < 9 then 1 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,1,1] else (if j.val < 4 then #[0,0,0,0,1] else #[0,0,0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,0,1] else #[0,0,1]) else (if j.val < 8 then #[0,0,0,1,1] else (if j.val < 9 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[2] else #[1,2]) else (if j.val < 3 then #[2,4,3,4] else (if j.val < 4 then #[1,2,3,4,3] else #[1,2,3,4,5,3]))) else (if j.val < 7 then (if j.val < 6 then #[1,3,6,4] else #[1,4,4]) else (if j.val < 8 then #[2,3,4,3,4] else (if j.val < 9 then #[10] else #[9,10]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 83).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 83).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 83) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D83

namespace D84

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 312 else (if j.val < 4 then 549 else 1085))) else (if j.val < 7 then (if j.val < 6 then 2095 else 4137) else (if j.val < 8 then 8199 else (if j.val < 9 then 16428 else 32781))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 84).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 84).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 4 else (if j.val < 4 then 4 else 5))) else (if j.val < 7 then (if j.val < 6 then 5 else 4) else (if j.val < 8 then 5 else (if j.val < 9 then 1 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,1,1] else (if j.val < 4 then #[0,0,0,1] else #[0,0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,0,0,1] else #[0,0,0,1]) else (if j.val < 8 then #[0,0,0,1,1] else (if j.val < 9 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[2] else #[1,2]) else (if j.val < 3 then #[1,4,3,4] else (if j.val < 4 then #[2,3,4,3] else #[2,3,4,5,3]))) else (if j.val < 7 then (if j.val < 6 then #[1,2,3,6,4] else #[1,2,4,4]) else (if j.val < 8 then #[1,3,4,3,4] else (if j.val < 9 then #[10] else #[9,10]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 84).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 84).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 84) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D84

namespace D85

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 287 else (if j.val < 4 then 571 else 1050))) else (if j.val < 7 then (if j.val < 6 then 2097 else 4110) else (if j.val < 8 then 8217 else (if j.val < 9 then 16395 else 32787))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 85).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 85).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 5 else (if j.val < 4 then 4 else 5))) else (if j.val < 7 then (if j.val < 6 then 4 else 3) else (if j.val < 8 then 6 else (if j.val < 9 then 1 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,0,1,1] else (if j.val < 4 then #[0,0,0,1] else #[0,0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,0,1] else #[0,0,1]) else (if j.val < 8 then #[0,0,0,0,1,1] else (if j.val < 9 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[2] else #[1,2]) else (if j.val < 3 then #[1,2,4,3,4] else (if j.val < 4 then #[1,3,4,3] else #[1,3,4,5,3]))) else (if j.val < 7 then (if j.val < 6 then #[2,3,6,4] else #[2,4,4]) else (if j.val < 8 then #[1,2,3,4,3,4] else (if j.val < 9 then #[10] else #[9,10]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 85).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 85).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 85) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D85

namespace D86

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 257 else (if j.val < 4 then 514 else 1028))) else (if j.val < 7 then (if j.val < 6 then 2056 else 4112) else (if j.val < 8 then 8224 else (if j.val < 9 then 16405 else 32810))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 86).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 86).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else (if j.val < 4 then 3 else 4))) else (if j.val < 7 then (if j.val < 6 then 3 else 2) else (if j.val < 8 then 4 else (if j.val < 9 then 1 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,1,1] else (if j.val < 4 then #[0,0,1] else #[0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,1] else #[0,1]) else (if j.val < 8 then #[0,0,1,1] else (if j.val < 9 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[2] else #[1,2]) else (if j.val < 3 then #[4,3,4] else (if j.val < 4 then #[3,4,3] else #[3,4,5,3]))) else (if j.val < 7 then (if j.val < 6 then #[3,6,4] else #[4,4]) else (if j.val < 8 then #[3,4,3,4] else (if j.val < 9 then #[10] else #[9,10]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 86).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 86).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 86) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D86

namespace D87

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 312 else (if j.val < 4 then 549 else 1085))) else (if j.val < 7 then (if j.val < 6 then 2095 else 4137) else (if j.val < 8 then 8199 else (if j.val < 9 then 16428 else 32781))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 87).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 87).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 4 else (if j.val < 4 then 4 else 5))) else (if j.val < 7 then (if j.val < 6 then 3 else 2) else (if j.val < 8 then 5 else (if j.val < 9 then 1 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,1,1] else (if j.val < 4 then #[0,0,0,1] else #[0,0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,1] else #[0,1]) else (if j.val < 8 then #[0,0,0,1,1] else (if j.val < 9 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[2] else #[1,2]) else (if j.val < 3 then #[1,4,3,4] else (if j.val < 4 then #[1,3,4,3] else #[1,3,4,5,3]))) else (if j.val < 7 then (if j.val < 6 then #[3,6,4] else #[4,4]) else (if j.val < 8 then #[1,3,4,3,4] else (if j.val < 9 then #[10] else #[9,10]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 87).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 87).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 87) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D87

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

end
