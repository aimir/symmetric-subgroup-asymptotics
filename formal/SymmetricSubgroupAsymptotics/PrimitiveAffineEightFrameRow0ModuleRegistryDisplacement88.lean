import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 88–95. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

local instance sourceGroupDisplacement88 : Group Source := PrimitiveAffineEightFrameRow0TopCertificate.group
local instance sourceInhabitedDisplacement88 : Inhabited Source := ⟨1⟩

namespace D88

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
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 88).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 88).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 4 else (if j.val < 4 then 3 else 4))) else (if j.val < 7 then (if j.val < 6 then 4 else 3) else (if j.val < 8 then 5 else (if j.val < 9 then 1 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,1,1] else (if j.val < 4 then #[0,0,1] else #[0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,0,1] else #[0,0,1]) else (if j.val < 8 then #[0,0,0,1,1] else (if j.val < 9 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[2] else #[1,2]) else (if j.val < 3 then #[1,4,3,4] else (if j.val < 4 then #[3,4,3] else #[3,4,5,3]))) else (if j.val < 7 then (if j.val < 6 then #[1,3,6,4] else #[1,4,4]) else (if j.val < 8 then #[1,3,4,3,4] else (if j.val < 9 then #[10] else #[9,10]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 88).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 88).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 88) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D88

namespace D89

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
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 89).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 89).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else (if j.val < 4 then 4 else 5))) else (if j.val < 7 then (if j.val < 6 then 4 else 3) else (if j.val < 8 then 4 else (if j.val < 9 then 1 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,1,1] else (if j.val < 4 then #[0,0,0,1] else #[0,0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,0,1] else #[0,0,1]) else (if j.val < 8 then #[0,0,1,1] else (if j.val < 9 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[2] else #[1,2]) else (if j.val < 3 then #[4,3,4] else (if j.val < 4 then #[1,3,4,3] else #[1,3,4,5,3]))) else (if j.val < 7 then (if j.val < 6 then #[1,3,6,4] else #[1,4,4]) else (if j.val < 8 then #[3,4,3,4] else (if j.val < 9 then #[10] else #[9,10]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 89).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 89).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 89) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D89

namespace D90

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 30 else 39) else (if j.val < 3 then 75 else (if j.val < 4 then 141 else 1285))) else (if j.val < 7 then (if j.val < 6 then 2570 else 4367) else (if j.val < 8 then 8709 else (if j.val < 9 then 16650 else 33295))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else (if j.val < 4 then 128 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 90).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 90).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 2 else (if j.val < 4 then 4 else 1))) else (if j.val < 7 then (if j.val < 6 then 1 else 4) else (if j.val < 8 then 2 else (if j.val < 9 then 3 else 6))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0] else (if j.val < 4 then #[0,0,0,0] else #[3]))) else (if j.val < 7 then (if j.val < 6 then #[3] else #[0,0,3,3]) else (if j.val < 8 then #[0,3] else (if j.val < 9 then #[0,0,3] else #[0,0,0,0,3,3]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0]) else (if j.val < 3 then #[1,5] else (if j.val < 4 then #[0,1,4,5] else #[0]))) else (if j.val < 7 then (if j.val < 6 then #[1] else #[6,7,0,1]) else (if j.val < 8 then #[6,0] else (if j.val < 9 then #[7,11,1] else #[6,7,10,11,0,1]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 90).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 90).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 90) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D90

namespace D91

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
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 91).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 91).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else (if j.val < 4 then 3 else 4))) else (if j.val < 7 then (if j.val < 6 then 3 else 2) else (if j.val < 8 then 4 else (if j.val < 9 then 1 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,1,1] else (if j.val < 4 then #[0,0,1] else #[0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,1] else #[0,1]) else (if j.val < 8 then #[0,0,1,1] else (if j.val < 9 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[3] else #[2,3]) else (if j.val < 3 then #[5,4,5] else (if j.val < 4 then #[4,5,4] else #[4,5,6,4]))) else (if j.val < 7 then (if j.val < 6 then #[4,7,5] else #[5,5]) else (if j.val < 8 then #[4,5,4,5] else (if j.val < 9 then #[11] else #[10,11]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 91).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 91).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 91) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D91

namespace D92

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
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 92).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 92).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 5 else (if j.val < 4 then 4 else 5))) else (if j.val < 7 then (if j.val < 6 then 4 else 3) else (if j.val < 8 then 6 else (if j.val < 9 then 1 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,0,1,1] else (if j.val < 4 then #[0,0,0,1] else #[0,0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,0,1] else #[0,0,1]) else (if j.val < 8 then #[0,0,0,0,1,1] else (if j.val < 9 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[3] else #[2,3]) else (if j.val < 3 then #[2,3,5,4,5] else (if j.val < 4 then #[3,4,5,4] else #[3,4,5,6,4]))) else (if j.val < 7 then (if j.val < 6 then #[2,4,7,5] else #[2,5,5]) else (if j.val < 8 then #[2,3,4,5,4,5] else (if j.val < 9 then #[11] else #[10,11]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 92).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 92).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 92) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D92

namespace D93

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
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 93).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 93).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 4 else (if j.val < 4 then 5 else 6))) else (if j.val < 7 then (if j.val < 6 then 4 else 3) else (if j.val < 8 then 5 else (if j.val < 9 then 1 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,1,1] else (if j.val < 4 then #[0,0,0,0,1] else #[0,0,0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,0,1] else #[0,0,1]) else (if j.val < 8 then #[0,0,0,1,1] else (if j.val < 9 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[3] else #[2,3]) else (if j.val < 3 then #[2,5,4,5] else (if j.val < 4 then #[2,3,4,5,4] else #[2,3,4,5,6,4]))) else (if j.val < 7 then (if j.val < 6 then #[3,4,7,5] else #[3,5,5]) else (if j.val < 8 then #[2,4,5,4,5] else (if j.val < 9 then #[11] else #[10,11]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 93).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 93).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 93) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D93

namespace D94

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
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 94).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 94).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 4 else (if j.val < 4 then 4 else 5))) else (if j.val < 7 then (if j.val < 6 then 5 else 4) else (if j.val < 8 then 5 else (if j.val < 9 then 1 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,1,1] else (if j.val < 4 then #[0,0,0,1] else #[0,0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,0,0,1] else #[0,0,0,1]) else (if j.val < 8 then #[0,0,0,1,1] else (if j.val < 9 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[3] else #[2,3]) else (if j.val < 3 then #[3,5,4,5] else (if j.val < 4 then #[2,4,5,4] else #[2,4,5,6,4]))) else (if j.val < 7 then (if j.val < 6 then #[2,3,4,7,5] else #[2,3,5,5]) else (if j.val < 8 then #[3,4,5,4,5] else (if j.val < 9 then #[11] else #[10,11]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 94).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 94).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 94) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D94

namespace D95

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 30 else (if j.val < 2 then 39 else 75)) else (if j.val < 4 then 141 else (if j.val < 5 then 257 else 514))) else (if j.val < 9 then (if j.val < 7 then 1028 else (if j.val < 8 then 2056 else 4110)) else (if j.val < 10 then 8199 else (if j.val < 11 then 16395 else 32781))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 16 else (if j.val < 2 then 32 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 95).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 95).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 2)) else (if j.val < 4 then 3 else (if j.val < 5 then 3 else 3))) else (if j.val < 9 then (if j.val < 7 then 4 else (if j.val < 8 then 3 else 4)) else (if j.val < 10 then 5 else (if j.val < 11 then 2 else 3))))

private def generatorRows (j : Fin 12) :
    Array (Fin 4) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,0])) else (if j.val < 4 then #[0,0,0] else (if j.val < 5 then #[0,1,1] else #[0,0,1]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,0,1] else (if j.val < 8 then #[0,0,1] else #[0,0,0,1])) else (if j.val < 10 then #[0,0,0,1,1] else (if j.val < 11 then #[0,0] else #[0,0,0]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 12) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0] else #[0,3])) else (if j.val < 4 then #[1,2,3] else (if j.val < 5 then #[5,4,5] else #[4,5,4]))) else (if j.val < 9 then (if j.val < 7 then #[4,5,6,4] else (if j.val < 8 then #[4,7,5] else #[0,1,5,5])) else (if j.val < 10 then #[0,4,5,4,5] else (if j.val < 11 then #[0,11] else #[1,10,11]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 95).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 95).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 95) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D95

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

end
