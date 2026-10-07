import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 16–31. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistry

local instance sourceGroupDisplacement16 : Group Source := PrimitiveAffineEightFrameRow3TopCertificate.group
local instance sourceInhabitedDisplacement16 : Inhabited Source := ⟨1⟩

namespace D16

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 16).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 16).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 2)) else (if j.val < 4 then 1 else (if j.val < 5 then 2 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,0])) else (if j.val < 4 then #[0] else (if j.val < 5 then #[0,0] else #[0,0,0])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0] else #[2,3])) else (if j.val < 4 then #[2] else (if j.val < 5 then #[2,5] else #[3,4,5])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 6 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 16).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 16).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 16) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D16

namespace D17

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 7737)) else (if j.val < 4 then 10023 else (if j.val < 5 then 19257 else 36135)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 17).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 17).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 2)) else (if j.val < 4 then 1 else (if j.val < 5 then 2 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,0])) else (if j.val < 4 then #[0] else (if j.val < 5 then #[0,0] else #[0,0,0])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0] else #[2,3])) else (if j.val < 4 then #[2] else (if j.val < 5 then #[2,5] else #[3,4,5])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 6 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 17).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 17).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 17) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D17

namespace D18

private def displacementBasis (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 6939 else (if j.val < 4 then 19995 else 43520)))

private def displacementDual (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 4096 else (if j.val < 4 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 5 :=
  binaryCoordinateSpaceOfMasks 16 5
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 18).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 18).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 1 else (if j.val < 4 then 2 else 2)))

private def generatorRows (j : Fin 5) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[5] else (if j.val < 4 then #[0,5] else #[0,0])))

private def stateBasisRows (j : Fin 5) :
    Array (Fin 7) :=
  (if j.val < 2 then (if j.val < 1 then #[1,2] else #[1]) else (if j.val < 3 then #[0] else (if j.val < 4 then #[6,0] else #[5,6])))

private def termGenerator (j : Fin 5)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 5)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 5)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 18).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 18).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 18) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D18

namespace D19

private def displacementBasis (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 11565 else (if j.val < 4 then 21760 else 34605)))

private def displacementDual (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 8192 else (if j.val < 4 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 5 :=
  binaryCoordinateSpaceOfMasks 16 5
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 19).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 19).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 1 else (if j.val < 4 then 1 else 3)))

private def generatorRows (j : Fin 5) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[5] else (if j.val < 4 then #[0] else #[0,0,5])))

private def stateBasisRows (j : Fin 5) :
    Array (Fin 7) :=
  (if j.val < 2 then (if j.val < 1 then #[1,2] else #[1]) else (if j.val < 3 then #[0] else (if j.val < 4 then #[6] else #[5,6,0])))

private def termGenerator (j : Fin 5)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 5)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 5)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 19).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 19).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 19) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D19

namespace D20

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 20).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 20).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 1 else (if j.val < 4 then 1 else 3)))

private def generatorRows (j : Fin 5) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[5] else (if j.val < 4 then #[0] else #[0,0,5])))

private def stateBasisRows (j : Fin 5) :
    Array (Fin 7) :=
  (if j.val < 2 then (if j.val < 1 then #[1,2] else #[1]) else (if j.val < 3 then #[0] else (if j.val < 4 then #[6] else #[5,6,0])))

private def termGenerator (j : Fin 5)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 5)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 5)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 20).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 20).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 20) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D20

namespace D21

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 7710)) else (if j.val < 4 then 10041 else (if j.val < 5 then 19230 else 36153)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 21).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 21).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 1)) else (if j.val < 4 then 1 else (if j.val < 5 then 1 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0])) else (if j.val < 4 then #[0] else (if j.val < 5 then #[0] else #[0,0,0])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0] else #[4])) else (if j.val < 4 then #[2] else (if j.val < 5 then #[6] else #[4,5,6])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 21).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 21).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 21) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D21

namespace D22

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 7737)) else (if j.val < 4 then 10023 else (if j.val < 5 then 19257 else 36135)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 22).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 22).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 1)) else (if j.val < 4 then 1 else (if j.val < 5 then 1 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0])) else (if j.val < 4 then #[0] else (if j.val < 5 then #[0] else #[0,0,0])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0] else #[4])) else (if j.val < 4 then #[2] else (if j.val < 5 then #[6] else #[4,5,6])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 22).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 22).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 22) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D22

namespace D23

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 23).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 23).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 1)) else (if j.val < 4 then 1 else (if j.val < 5 then 1 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0])) else (if j.val < 4 then #[0] else (if j.val < 5 then #[0] else #[0,0,0])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0] else #[4])) else (if j.val < 4 then #[2] else (if j.val < 5 then #[6] else #[4,5,6])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 23).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 23).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 23) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D23

namespace D24

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 7737)) else (if j.val < 4 then 10023 else (if j.val < 5 then 19257 else 36135)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 24).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 24).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 1)) else (if j.val < 4 then 2 else (if j.val < 5 then 2 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0])) else (if j.val < 4 then #[0,0] else (if j.val < 5 then #[0,0] else #[0,0,0])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0] else #[3])) else (if j.val < 4 then #[2,3] else (if j.val < 5 then #[3,6] else #[2,5,6])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 24).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 24).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 24) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D24

namespace D25

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 7710)) else (if j.val < 4 then 10041 else (if j.val < 5 then 19230 else 36153)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 25).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 25).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 1)) else (if j.val < 4 then 2 else (if j.val < 5 then 2 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0])) else (if j.val < 4 then #[0,0] else (if j.val < 5 then #[0,0] else #[0,0,0])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0] else #[3])) else (if j.val < 4 then #[2,3] else (if j.val < 5 then #[3,6] else #[2,5,6])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 25).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 25).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 25) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D25

namespace D26

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 26).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 26).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 1)) else (if j.val < 4 then 2 else (if j.val < 5 then 2 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0])) else (if j.val < 4 then #[0,0] else (if j.val < 5 then #[0,0] else #[0,0,0])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0] else #[3])) else (if j.val < 4 then #[2,3] else (if j.val < 5 then #[3,6] else #[2,5,6])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 26).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 26).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 26) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D26

namespace D27

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 27).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 27).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 1)) else (if j.val < 4 then 2 else (if j.val < 5 then 2 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0])) else (if j.val < 4 then #[0,0] else (if j.val < 5 then #[0,0] else #[0,0,0])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0] else #[2])) else (if j.val < 4 then #[2,3] else (if j.val < 5 then #[3,6] else #[3,5,6])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 27).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 27).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 27) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D27

namespace D28

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 7710)) else (if j.val < 4 then 10041 else (if j.val < 5 then 19230 else 36153)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 28).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 28).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 1)) else (if j.val < 4 then 2 else (if j.val < 5 then 2 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0])) else (if j.val < 4 then #[0,0] else (if j.val < 5 then #[0,0] else #[0,0,0])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0] else #[2])) else (if j.val < 4 then #[2,3] else (if j.val < 5 then #[3,6] else #[3,5,6])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 28).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 28).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 28) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D28

namespace D29

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 7737)) else (if j.val < 4 then 10023 else (if j.val < 5 then 19257 else 36135)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 29).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 29).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 1)) else (if j.val < 4 then 2 else (if j.val < 5 then 2 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0])) else (if j.val < 4 then #[0,0] else (if j.val < 5 then #[0,0] else #[0,0,0])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0] else #[2])) else (if j.val < 4 then #[2,3] else (if j.val < 5 then #[3,6] else #[3,5,6])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 29).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 29).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 29) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D29

namespace D30

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 30).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 30).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 1)) else (if j.val < 4 then 1 else (if j.val < 5 then 2 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[5])) else (if j.val < 4 then #[5] else (if j.val < 5 then #[0,5] else #[0,0,5])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[2,3] else (if j.val < 2 then #[2] else #[0])) else (if j.val < 4 then #[1] else (if j.val < 5 then #[7,0] else #[6,7,1])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 30).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 30).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 30) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D30

namespace D31

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 31).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 31).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 2)) else (if j.val < 5 then (if j.val < 4 then 1 else 3) else (if j.val < 6 then 1 else 3)))

private def generatorRows (j : Fin 7) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,5])) else (if j.val < 5 then (if j.val < 4 then #[5] else #[0,0,5]) else (if j.val < 6 then #[0] else #[0,0,5])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[1,2] else (if j.val < 2 then #[1] else #[5,0])) else (if j.val < 5 then (if j.val < 4 then #[0] else #[3,5,0]) else (if j.val < 6 then #[7] else #[6,7,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 31).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 31).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 31) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D31

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistry

end
