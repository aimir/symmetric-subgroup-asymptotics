import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 0–7. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistry

local instance sourceGroupDisplacement0 : Group Source := PrimitiveAffineEightFrameTop10TopCertificate.group
local instance sourceInhabitedDisplacement0 : Inhabited Source := ⟨1⟩

namespace D0

private def displacementBasis (j : Fin 0) : ℕ :=
  0

private def displacementDual (j : Fin 0) : ℕ :=
  0

def displacementChart :
    BinaryCoordinateSpace 16 0 :=
  binaryCoordinateSpaceOfMasks 16 0
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 0).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 0).2.mem_iff _).mpr
  exact Fin.elim0 j

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow19ModuleRepresentation.representation PrimitiveAffineEightFrameTop10TopCertificate.ambient
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 0) displacementChart where
  space_le_state := displacement_le_state
  termCount := fun j ↦ Fin.elim0 j
  termGenerator := fun j ↦ Fin.elim0 j
  termVector := fun j ↦ Fin.elim0 j
  basis_eq := fun j ↦ Fin.elim0 j

end D0

namespace D1

private def displacementBasis (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 21760 else 43520))

private def displacementDual (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 16384 else 32768))

def displacementChart :
    BinaryCoordinateSpace 16 4 :=
  binaryCoordinateSpaceOfMasks 16 4
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 1).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 1).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 1 else 2))

private def generatorRows (j : Fin 4) :
    Array (Fin 9) :=
  (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[3] else #[3,3]))

private def stateBasisRows (j : Fin 4) :
    Array (Fin 4) :=
  (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[3] else #[2,3]))

private def termGenerator (j : Fin 4)
    (t : Fin (termCount j)) : Fin 9 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 4)
    (t : Fin (termCount j)) : Fin 4 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 4)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 1).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 1).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow19ModuleRepresentation.representation PrimitiveAffineEightFrameTop10TopCertificate.ambient
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 1) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D1

namespace D2

private def displacementBasis (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 21760 else 43520))

private def displacementDual (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 16384 else 32768))

def displacementChart :
    BinaryCoordinateSpace 16 4 :=
  binaryCoordinateSpaceOfMasks 16 4
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 2).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 2).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 1 else 2))

private def generatorRows (j : Fin 4) :
    Array (Fin 9) :=
  (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[3] else #[3,3]))

private def stateBasisRows (j : Fin 4) :
    Array (Fin 5) :=
  (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[4] else #[3,4]))

private def termGenerator (j : Fin 4)
    (t : Fin (termCount j)) : Fin 9 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 4)
    (t : Fin (termCount j)) : Fin 5 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 4)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 2).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 2).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow19ModuleRepresentation.representation PrimitiveAffineEightFrameTop10TopCertificate.ambient
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 2) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D2

namespace D3

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
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 3).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 3).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 1 else (if j.val < 4 then 1 else 3)))

private def generatorRows (j : Fin 5) :
    Array (Fin 9) :=
  (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[8] else (if j.val < 4 then #[3] else #[3,3,8])))

private def stateBasisRows (j : Fin 5) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[2] else #[1,2]) else (if j.val < 3 then #[0] else (if j.val < 4 then #[5] else #[4,5,0])))

private def termGenerator (j : Fin 5)
    (t : Fin (termCount j)) : Fin 9 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 5)
    (t : Fin (termCount j)) : Fin 6 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 5)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 3).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 3).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow19ModuleRepresentation.representation PrimitiveAffineEightFrameTop10TopCertificate.ambient
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 3) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D3

namespace D4

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 54 else (if j.val < 2 then 85 else 156)) else (if j.val < 4 then 13824 else (if j.val < 5 then 21760 else 39936)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 32 else (if j.val < 2 then 64 else 128)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 4).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 4).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 3 else (if j.val < 2 then 1 else 1)) else (if j.val < 4 then 3 else (if j.val < 5 then 1 else 1)))

private def generatorRows (j : Fin 6) :
    Array (Fin 9) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0,7] else (if j.val < 2 then #[0] else #[7])) else (if j.val < 4 then #[3,3,6] else (if j.val < 5 then #[3] else #[6])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[1,2,3] else (if j.val < 2 then #[2] else #[3])) else (if j.val < 4 then #[5,6,3] else (if j.val < 5 then #[6] else #[3])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 9 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 4).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 4).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow19ModuleRepresentation.representation PrimitiveAffineEightFrameTop10TopCertificate.ambient
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 4) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D4

namespace D5

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 54 else (if j.val < 2 then 85 else 156)) else (if j.val < 5 then (if j.val < 4 then 6939 else 11547) else (if j.val < 6 then 19995 else 34587)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 32 else (if j.val < 2 then 64 else 128)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 5).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 5).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 3 else (if j.val < 2 then 1 else 1)) else (if j.val < 5 then (if j.val < 4 then 1 else 4) else (if j.val < 6 then 2 else 2)))

private def generatorRows (j : Fin 7) :
    Array (Fin 9) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0,7] else (if j.val < 2 then #[0] else #[7])) else (if j.val < 5 then (if j.val < 4 then #[8] else #[3,3,6,8]) else (if j.val < 6 then #[3,8] else #[6,8])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[2,3,0] else (if j.val < 2 then #[3] else #[0])) else (if j.val < 5 then (if j.val < 4 then #[0] else #[6,7,4,0]) else (if j.val < 6 then #[7,0] else #[4,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 9 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 5).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 5).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow19ModuleRepresentation.representation PrimitiveAffineEightFrameTop10TopCertificate.ambient
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 5) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D5

namespace D6

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
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 6).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 6).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 2 else 1) else (if j.val < 7 then 2 else 3)))

private def generatorRows (j : Fin 8) :
    Array (Fin 9) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0] else #[0,0,0])) else (if j.val < 6 then (if j.val < 5 then #[3,3] else #[3]) else (if j.val < 7 then #[3,3] else #[3,3,3])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0]) else (if j.val < 3 then #[0,3] else #[1,2,3])) else (if j.val < 6 then (if j.val < 5 then #[4,5] else #[4]) else (if j.val < 7 then #[4,7] else #[5,6,7])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 9 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 6).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 6).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow19ModuleRepresentation.representation PrimitiveAffineEightFrameTop10TopCertificate.ambient
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 6) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D6

namespace D7

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
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 7).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 7).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 1 else 2) else (if j.val < 7 then 2 else 3)))

private def generatorRows (j : Fin 8) :
    Array (Fin 9) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0] else #[0,0,0])) else (if j.val < 6 then (if j.val < 5 then #[3] else #[3,3]) else (if j.val < 7 then #[3,3] else #[3,3,3])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 9) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0]) else (if j.val < 3 then #[0,3] else #[1,2,3])) else (if j.val < 6 then (if j.val < 5 then #[4] else #[4,5]) else (if j.val < 7 then #[5,8] else #[5,7,8])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 9 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 7).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 7).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow19ModuleRepresentation.representation PrimitiveAffineEightFrameTop10TopCertificate.ambient
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 7) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D7

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistry

end
