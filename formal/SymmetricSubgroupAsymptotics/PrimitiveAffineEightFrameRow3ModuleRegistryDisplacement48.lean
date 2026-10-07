import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 48–63. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistry

local instance sourceGroupDisplacement48 : Group Source := PrimitiveAffineEightFrameRow3TopCertificate.group
local instance sourceInhabitedDisplacement48 : Inhabited Source := ⟨1⟩

namespace D48

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 1314)) else (if j.val < 5 then (if j.val < 4 then 6939 else 8709) else (if j.val < 6 then 19257 else 34821)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 1024)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 48).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 48).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 3)) else (if j.val < 5 then (if j.val < 4 then 1 else 2) else (if j.val < 6 then 2 else 3)))

private def generatorRows (j : Fin 7) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,0,5])) else (if j.val < 5 then (if j.val < 4 then #[5] else #[0,5]) else (if j.val < 6 then #[0,0] else #[0,0,5])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0] else #[2,3,3])) else (if j.val < 5 then (if j.val < 4 then #[3] else #[3,3]) else (if j.val < 6 then #[3,7] else #[6,7,3])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 48).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 48).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 48) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D48

namespace D49

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 2580)) else (if j.val < 5 then (if j.val < 4 then 5130 else 10041) else (if j.val < 6 then 16650 else 34605)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 2048)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 49).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 49).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 2)) else (if j.val < 5 then (if j.val < 4 then 2 else 1) else (if j.val < 6 then 4 else 4)))

private def generatorRows (j : Fin 7) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,5])) else (if j.val < 5 then (if j.val < 4 then #[0,5] else #[0]) else (if j.val < 6 then #[0,0,0,5] else #[0,0,0,5])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0] else #[2,2])) else (if j.val < 5 then (if j.val < 4 then #[3,2] else #[2]) else (if j.val < 6 then #[2,3,7,2] else #[3,6,7,2])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 49).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 49).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 49) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D49

namespace D50

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 3857)) else (if j.val < 5 then (if j.val < 4 then 4367 else 10041) else (if j.val < 6 then 17423 else 33320)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 2048)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 50).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 50).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 2)) else (if j.val < 5 then (if j.val < 4 then 2 else 1) else (if j.val < 6 then 2 else 4)))

private def generatorRows (j : Fin 7) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,5])) else (if j.val < 5 then (if j.val < 4 then #[0,5] else #[0]) else (if j.val < 6 then #[0,5] else #[0,0,0,5])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0] else #[3,2])) else (if j.val < 5 then (if j.val < 4 then #[2,2] else #[2]) else (if j.val < 6 then #[7,2] else #[2,6,7,2])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 50).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 50).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 50) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D50

namespace D51

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 1340)) else (if j.val < 5 then (if j.val < 4 then 6939 else 8738) else (if j.val < 6 then 19239 else 34850)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 1024)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 51).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 51).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 2)) else (if j.val < 5 then (if j.val < 4 then 2 else 1) else (if j.val < 6 then 2 else 4)))

private def generatorRows (j : Fin 7) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,5])) else (if j.val < 5 then (if j.val < 4 then #[0,5] else #[5]) else (if j.val < 6 then #[0,0] else #[0,0,0,5])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0] else #[2,3])) else (if j.val < 5 then (if j.val < 4 then #[3,3] else #[3]) else (if j.val < 6 then #[3,7] else #[3,6,7,3])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 51).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 51).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 51) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D51

namespace D52

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 7719)) else (if j.val < 4 then 10014 else (if j.val < 5 then 19239 else 36126)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 52).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 52).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 2)) else (if j.val < 4 then 1 else (if j.val < 5 then 2 else 4)))

private def generatorRows (j : Fin 6) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,0])) else (if j.val < 4 then #[0] else (if j.val < 5 then #[0,0] else #[0,0,0,0])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0] else #[2,3])) else (if j.val < 4 then #[2] else (if j.val < 5 then #[3,7] else #[2,3,6,7])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 52).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 52).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 52) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D52

namespace D53

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 1285)) else (if j.val < 5 then (if j.val < 4 then 6939 else 8764) else (if j.val < 6 then 19230 else 34876)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 1024)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 53).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 53).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 3)) else (if j.val < 5 then (if j.val < 4 then 1 else 2) else (if j.val < 6 then 2 else 3)))

private def generatorRows (j : Fin 7) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,0,5])) else (if j.val < 5 then (if j.val < 4 then #[5] else #[0,5]) else (if j.val < 6 then #[0,0] else #[0,0,5])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 9) :=
  (if j.val < 3 then (if j.val < 1 then #[1,2] else (if j.val < 2 then #[1] else #[3,4,0])) else (if j.val < 5 then (if j.val < 4 then #[0] else #[4,0]) else (if j.val < 6 then #[4,8] else #[7,8,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 53).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 53).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 53) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D53

namespace D54

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 1314)) else (if j.val < 5 then (if j.val < 4 then 6939 else 8709) else (if j.val < 6 then 19257 else 34821)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 1024)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 54).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 54).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 3)) else (if j.val < 5 then (if j.val < 4 then 1 else 2) else (if j.val < 6 then 2 else 3)))

private def generatorRows (j : Fin 7) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,0,5])) else (if j.val < 5 then (if j.val < 4 then #[5] else #[0,5]) else (if j.val < 6 then #[0,0] else #[0,0,5])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 9) :=
  (if j.val < 3 then (if j.val < 1 then #[1,2] else (if j.val < 2 then #[1] else #[3,4,0])) else (if j.val < 5 then (if j.val < 4 then #[0] else #[4,0]) else (if j.val < 6 then #[4,8] else #[7,8,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 54).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 54).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 54) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D54

namespace D55

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 1340)) else (if j.val < 5 then (if j.val < 4 then 6939 else 8738) else (if j.val < 6 then 19239 else 34850)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 1024)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 55).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 55).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 3)) else (if j.val < 5 then (if j.val < 4 then 1 else 2) else (if j.val < 6 then 2 else 3)))

private def generatorRows (j : Fin 7) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,0,5])) else (if j.val < 5 then (if j.val < 4 then #[5] else #[0,5]) else (if j.val < 6 then #[0,0] else #[0,0,5])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 9) :=
  (if j.val < 3 then (if j.val < 1 then #[1,2] else (if j.val < 2 then #[1] else #[3,4,0])) else (if j.val < 5 then (if j.val < 4 then #[0] else #[4,0]) else (if j.val < 6 then #[4,8] else #[7,8,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 55).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 55).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 55) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D55

namespace D56

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 56).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 56).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 2 else 2) else (if j.val < 7 then 2 else 3)))

private def generatorRows (j : Fin 8) :
    Array (Fin 6) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,0] else #[0,0])) else (if j.val < 6 then (if j.val < 5 then #[0,0] else #[0,0]) else (if j.val < 7 then #[0,0] else #[0,0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 9) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[0,2,3] else #[1,2])) else (if j.val < 6 then (if j.val < 5 then #[0,6] else #[0,4]) else (if j.val < 7 then #[0,8] else #[6,7,8])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 56).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 56).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 56) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D56

namespace D57

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 57).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 57).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 2 else 2) else (if j.val < 7 then 2 else 4)))

private def generatorRows (j : Fin 8) :
    Array (Fin 6) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,0] else #[0,0])) else (if j.val < 6 then (if j.val < 5 then #[0,0] else #[0,0]) else (if j.val < 7 then #[0,0] else #[0,0,0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 9) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[0,2,3] else #[1,2])) else (if j.val < 6 then (if j.val < 5 then #[1,5] else #[4,5]) else (if j.val < 7 then #[5,8] else #[1,4,7,8])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 57).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 57).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 57) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D57

namespace D58

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 58).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 58).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 3 else 2) else (if j.val < 7 then 2 else 5)))

private def generatorRows (j : Fin 8) :
    Array (Fin 6) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,0] else #[0,0])) else (if j.val < 6 then (if j.val < 5 then #[0,0,0] else #[0,0]) else (if j.val < 7 then #[0,0] else #[0,0,0,0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 9) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[0,2,3] else #[1,2])) else (if j.val < 6 then (if j.val < 5 then #[0,1,4] else #[4,5]) else (if j.val < 7 then #[5,8] else #[0,1,5,7,8])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 58).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 58).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 58) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D58

namespace D59

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 2580)) else (if j.val < 5 then (if j.val < 4 then 5130 else 10041) else (if j.val < 6 then 16650 else 34605)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 2048)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 59).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 59).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 2)) else (if j.val < 5 then (if j.val < 4 then 2 else 1) else (if j.val < 6 then 4 else 4)))

private def generatorRows (j : Fin 7) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,5])) else (if j.val < 5 then (if j.val < 4 then #[0,5] else #[0]) else (if j.val < 6 then #[0,0,0,5] else #[0,0,0,5])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 9) :=
  (if j.val < 3 then (if j.val < 1 then #[1,2] else (if j.val < 2 then #[1] else #[3,0])) else (if j.val < 5 then (if j.val < 4 then #[4,0] else #[3]) else (if j.val < 6 then #[3,4,8,0] else #[4,7,8,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 59).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 59).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 59) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D59

namespace D60

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 2570)) else (if j.val < 5 then (if j.val < 4 then 5171 else 10023) else (if j.val < 6 then 16691 else 34605)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 2048)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 60).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 60).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 2)) else (if j.val < 5 then (if j.val < 4 then 2 else 1) else (if j.val < 6 then 4 else 4)))

private def generatorRows (j : Fin 7) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,5])) else (if j.val < 5 then (if j.val < 4 then #[0,5] else #[0]) else (if j.val < 6 then #[0,0,0,5] else #[0,0,0,5])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 9) :=
  (if j.val < 3 then (if j.val < 1 then #[1,2] else (if j.val < 2 then #[1] else #[3,0])) else (if j.val < 5 then (if j.val < 4 then #[4,0] else #[3]) else (if j.val < 6 then #[3,4,8,0] else #[4,7,8,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 60).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 60).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 60) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D60

namespace D61

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 2611)) else (if j.val < 5 then (if j.val < 4 then 5140 else 10014) else (if j.val < 6 then 16660 else 34605)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 2048)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 61).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 61).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 2)) else (if j.val < 5 then (if j.val < 4 then 2 else 1) else (if j.val < 6 then 4 else 4)))

private def generatorRows (j : Fin 7) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,5])) else (if j.val < 5 then (if j.val < 4 then #[0,5] else #[0]) else (if j.val < 6 then #[0,0,0,5] else #[0,0,0,5])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 9) :=
  (if j.val < 3 then (if j.val < 1 then #[1,2] else (if j.val < 2 then #[1] else #[3,0])) else (if j.val < 5 then (if j.val < 4 then #[4,0] else #[3]) else (if j.val < 6 then #[3,4,8,0] else #[4,7,8,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 61).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 61).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 61) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D61

namespace D62

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 3857)) else (if j.val < 5 then (if j.val < 4 then 4367 else 10041) else (if j.val < 6 then 17423 else 33320)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 2048)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 62).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 62).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 2)) else (if j.val < 5 then (if j.val < 4 then 2 else 1) else (if j.val < 6 then 2 else 4)))

private def generatorRows (j : Fin 7) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,5])) else (if j.val < 5 then (if j.val < 4 then #[0,5] else #[0]) else (if j.val < 6 then #[0,5] else #[0,0,0,5])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 9) :=
  (if j.val < 3 then (if j.val < 1 then #[1,2] else (if j.val < 2 then #[1] else #[4,0])) else (if j.val < 5 then (if j.val < 4 then #[3,0] else #[3]) else (if j.val < 6 then #[8,0] else #[3,7,8,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 62).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 62).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 62) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D62

namespace D63

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 3855)) else (if j.val < 5 then (if j.val < 4 then 4392 else 10014) else (if j.val < 6 then 17448 else 33297)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 2048)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 63).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 63).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 2)) else (if j.val < 5 then (if j.val < 4 then 2 else 1) else (if j.val < 6 then 2 else 4)))

private def generatorRows (j : Fin 7) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,5])) else (if j.val < 5 then (if j.val < 4 then #[0,5] else #[0]) else (if j.val < 6 then #[0,5] else #[0,0,0,5])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 9) :=
  (if j.val < 3 then (if j.val < 1 then #[1,2] else (if j.val < 2 then #[1] else #[4,0])) else (if j.val < 5 then (if j.val < 4 then #[3,0] else #[3]) else (if j.val < 6 then #[8,0] else #[3,7,8,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 63).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 63).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 63) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D63

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistry

end
