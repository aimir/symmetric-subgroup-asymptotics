import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 40–47. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

local instance sourceGroupDisplacement40 : Group Source := PrimitiveAffineEightFrameRow0TopCertificate.group
local instance sourceInhabitedDisplacement40 : Inhabited Source := ⟨1⟩

namespace D40

private def displacementBasis (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 13878 else (if j.val < 4 then 21760 else 39990)))

private def displacementDual (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 8192 else (if j.val < 4 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 5 :=
  binaryCoordinateSpaceOfMasks 16 5
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 40).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 40).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 1 else (if j.val < 4 then 1 else 3)))

private def generatorRows (j : Fin 5) :
    Array (Fin 4) :=
  (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[3] else (if j.val < 4 then #[0] else #[0,0,3])))

private def stateBasisRows (j : Fin 5) :
    Array (Fin 7) :=
  (if j.val < 2 then (if j.val < 1 then #[2] else #[1,2]) else (if j.val < 3 then #[0] else (if j.val < 4 then #[6] else #[5,6,0])))

private def termGenerator (j : Fin 5)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 5)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 5)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 40).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 40).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 40) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D40

namespace D41

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 7710)) else (if j.val < 4 then 10023 else (if j.val < 5 then 19230 else 36135)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 41).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 41).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 1)) else (if j.val < 4 then 1 else (if j.val < 5 then 1 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 4) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,0] else #[0])) else (if j.val < 4 then #[0] else (if j.val < 5 then #[0] else #[0,0,0])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[1] else (if j.val < 2 then #[0,1] else #[4])) else (if j.val < 4 then #[2] else (if j.val < 5 then #[6] else #[4,5,6])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 41).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 41).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 41) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D41

namespace D42

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 7710)) else (if j.val < 4 then 10023 else (if j.val < 5 then 19230 else 36135)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 42).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 42).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 1)) else (if j.val < 4 then 2 else (if j.val < 5 then 2 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 4) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,0] else #[0])) else (if j.val < 4 then #[0,0] else (if j.val < 5 then #[0,0] else #[0,0,0])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[1] else (if j.val < 2 then #[0,1] else #[3])) else (if j.val < 4 then #[2,3] else (if j.val < 5 then #[3,6] else #[2,5,6])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 42).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 42).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 42) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D42

namespace D43

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 7710)) else (if j.val < 4 then 10023 else (if j.val < 5 then 19230 else 36135)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 43).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 43).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 1)) else (if j.val < 4 then 2 else (if j.val < 5 then 2 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 4) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,0] else #[0])) else (if j.val < 4 then #[0,0] else (if j.val < 5 then #[0,0] else #[0,0,0])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[1] else (if j.val < 2 then #[0,1] else #[2])) else (if j.val < 4 then #[2,3] else (if j.val < 5 then #[3,6] else #[3,5,6])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 43).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 43).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 43) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D43

namespace D44

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 6939)) else (if j.val < 4 then 11565 else (if j.val < 5 then 19995 else 34605)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 44).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 44).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 1)) else (if j.val < 4 then 1 else (if j.val < 5 then 2 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 4) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,0] else #[3])) else (if j.val < 4 then #[3] else (if j.val < 5 then #[0,3] else #[0,0,3])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[3] else (if j.val < 2 then #[2,3] else #[0])) else (if j.val < 4 then #[1] else (if j.val < 5 then #[7,0] else #[6,7,1])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 44).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 44).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 44) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D44

namespace D45

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 1285)) else (if j.val < 5 then (if j.val < 4 then 6939 else 8738) else (if j.val < 6 then 19230 else 34850)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 1024)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 45).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 45).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 2)) else (if j.val < 5 then (if j.val < 4 then 1 else 3) else (if j.val < 6 then 1 else 3)))

private def generatorRows (j : Fin 7) :
    Array (Fin 4) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,0] else #[0,3])) else (if j.val < 5 then (if j.val < 4 then #[3] else #[0,0,3]) else (if j.val < 6 then #[0] else #[0,0,3])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[2] else (if j.val < 2 then #[1,2] else #[5,0])) else (if j.val < 5 then (if j.val < 4 then #[0] else #[3,5,0]) else (if j.val < 6 then #[7] else #[6,7,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 45).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 45).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 45) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D45

namespace D46

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 30 else 39) else (if j.val < 3 then 75 else 141)) else (if j.val < 6 then (if j.val < 5 then 7680 else 9984) else (if j.val < 7 then 19200 else 36096)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else 128)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 46).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 46).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 2 else 1) else (if j.val < 7 then 2 else 3)))

private def generatorRows (j : Fin 8) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0] else #[0,0,0])) else (if j.val < 6 then (if j.val < 5 then #[0,0] else #[0]) else (if j.val < 7 then #[0,0] else #[0,0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0]) else (if j.val < 3 then #[0,3] else #[1,2,3])) else (if j.val < 6 then (if j.val < 5 then #[4,5] else #[4]) else (if j.val < 7 then #[4,7] else #[5,6,7])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 46).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 46).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 46) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D46

namespace D47

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 2570)) else (if j.val < 5 then (if j.val < 4 then 5140 else 10023) else (if j.val < 6 then 16660 else 34605)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 2048)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 47).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 47).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 3)) else (if j.val < 5 then (if j.val < 4 then 2 else 2) else (if j.val < 6 then 3 else 4)))

private def generatorRows (j : Fin 7) :
    Array (Fin 4) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,0] else #[0,0,3])) else (if j.val < 5 then (if j.val < 4 then #[0,3] else #[0,0]) else (if j.val < 6 then #[0,0,3] else #[0,0,0,3])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[2] else (if j.val < 2 then #[1,2] else #[3,4,0])) else (if j.val < 5 then (if j.val < 4 then #[3,0] else #[3,4]) else (if j.val < 6 then #[3,7,0] else #[4,6,7,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 47).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 47).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 47) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D47

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

end
