import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 0–7. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistry

local instance sourceGroupDisplacement0 : Group Source := PrimitiveAffineEightFrameTop13TopCertificate.group
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
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 0).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 0).2.mem_iff _).mpr
  exact Fin.elim0 j

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow22ModuleRepresentation.representation PrimitiveAffineEightFrameTop13TopCertificate.ambient
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 0) displacementChart where
  space_le_state := displacement_le_state
  termCount := fun j ↦ Fin.elim0 j
  termGenerator := fun j ↦ Fin.elim0 j
  termVector := fun j ↦ Fin.elim0 j
  basis_eq := fun j ↦ Fin.elim0 j

end D0

namespace D1

private def displacementBasis (j : Fin 2) : ℕ :=
  (if j.val < 1 then 21845 else 43690)

private def displacementDual (j : Fin 2) : ℕ :=
  (if j.val < 1 then 16384 else 32768)

def displacementChart :
    BinaryCoordinateSpace 16 2 :=
  binaryCoordinateSpaceOfMasks 16 2
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 1).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 1).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 2) : ℕ :=
  (if j.val < 1 then 1 else 2)

private def generatorRows (j : Fin 2) :
    Array (Fin 6) :=
  (if j.val < 1 then #[4] else #[4,4])

private def stateBasisRows (j : Fin 2) :
    Array (Fin 2) :=
  (if j.val < 1 then #[1] else #[0,1])

private def termGenerator (j : Fin 2)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 2)
    (t : Fin (termCount j)) : Fin 2 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 2)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 1).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 1).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow22ModuleRepresentation.representation PrimitiveAffineEightFrameTop13TopCertificate.ambient
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 1) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D1

namespace D2

private def displacementBasis (j : Fin 2) : ℕ :=
  (if j.val < 1 then 21845 else 43690)

private def displacementDual (j : Fin 2) : ℕ :=
  (if j.val < 1 then 16384 else 32768)

def displacementChart :
    BinaryCoordinateSpace 16 2 :=
  binaryCoordinateSpaceOfMasks 16 2
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 2).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 2).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 2) : ℕ :=
  (if j.val < 1 then 1 else 2)

private def generatorRows (j : Fin 2) :
    Array (Fin 6) :=
  (if j.val < 1 then #[4] else #[4,4])

private def stateBasisRows (j : Fin 2) :
    Array (Fin 3) :=
  (if j.val < 1 then #[2] else #[0,2])

private def termGenerator (j : Fin 2)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 2)
    (t : Fin (termCount j)) : Fin 3 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 2)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 2).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 2).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow22ModuleRepresentation.representation PrimitiveAffineEightFrameTop13TopCertificate.ambient
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 2) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D2

namespace D3

private def displacementBasis (j : Fin 2) : ℕ :=
  (if j.val < 1 then 21845 else 43690)

private def displacementDual (j : Fin 2) : ℕ :=
  (if j.val < 1 then 16384 else 32768)

def displacementChart :
    BinaryCoordinateSpace 16 2 :=
  binaryCoordinateSpaceOfMasks 16 2
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 3).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 3).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 2) : ℕ :=
  (if j.val < 1 then 1 else 2)

private def generatorRows (j : Fin 2) :
    Array (Fin 6) :=
  (if j.val < 1 then #[4] else #[4,4])

private def stateBasisRows (j : Fin 2) :
    Array (Fin 3) :=
  (if j.val < 1 then #[0] else #[0,1])

private def termGenerator (j : Fin 2)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 2)
    (t : Fin (termCount j)) : Fin 3 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 2)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 3).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 3).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow22ModuleRepresentation.representation PrimitiveAffineEightFrameTop13TopCertificate.ambient
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 3) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D3

namespace D4

private def displacementBasis (j : Fin 2) : ℕ :=
  (if j.val < 1 then 21845 else 43690)

private def displacementDual (j : Fin 2) : ℕ :=
  (if j.val < 1 then 16384 else 32768)

def displacementChart :
    BinaryCoordinateSpace 16 2 :=
  binaryCoordinateSpaceOfMasks 16 2
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 4).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 4).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 2) : ℕ :=
  (if j.val < 1 then 2 else 1)

private def generatorRows (j : Fin 2) :
    Array (Fin 6) :=
  (if j.val < 1 then #[4,4] else #[4])

private def stateBasisRows (j : Fin 2) :
    Array (Fin 3) :=
  (if j.val < 1 then #[0,1] else #[0])

private def termGenerator (j : Fin 2)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 2)
    (t : Fin (termCount j)) : Fin 3 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 2)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 4).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 4).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow22ModuleRepresentation.representation PrimitiveAffineEightFrameTop13TopCertificate.ambient
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 4) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D4

namespace D5

private def displacementBasis (j : Fin 2) : ℕ :=
  (if j.val < 1 then 21845 else 43690)

private def displacementDual (j : Fin 2) : ℕ :=
  (if j.val < 1 then 16384 else 32768)

def displacementChart :
    BinaryCoordinateSpace 16 2 :=
  binaryCoordinateSpaceOfMasks 16 2
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 5).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 5).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 2) : ℕ :=
  (if j.val < 1 then 1 else 2)

private def generatorRows (j : Fin 2) :
    Array (Fin 6) :=
  (if j.val < 1 then #[4] else #[4,4])

private def stateBasisRows (j : Fin 2) :
    Array (Fin 4) :=
  (if j.val < 1 then #[1] else #[0,1])

private def termGenerator (j : Fin 2)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 2)
    (t : Fin (termCount j)) : Fin 4 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 2)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 5).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 5).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow22ModuleRepresentation.representation PrimitiveAffineEightFrameTop13TopCertificate.ambient
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 5) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D5

namespace D6

private def displacementBasis (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1530 else 2655) else (if j.val < 3 then 20655 else 41205))

private def displacementDual (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1024 else 2048) else (if j.val < 3 then 16384 else 32768))

def displacementChart :
    BinaryCoordinateSpace 16 4 :=
  binaryCoordinateSpaceOfMasks 16 4
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 6).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 6).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 2 else 3) else (if j.val < 3 then 2 else 1))

private def generatorRows (j : Fin 4) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[4,4] else #[4,4,4]) else (if j.val < 3 then #[4,4] else #[4]))

private def stateBasisRows (j : Fin 4) :
    Array (Fin 4) :=
  (if j.val < 2 then (if j.val < 1 then #[1,2] else #[0,1,3]) else (if j.val < 3 then #[2,3] else #[2]))

private def termGenerator (j : Fin 4)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 4)
    (t : Fin (termCount j)) : Fin 4 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 4)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 6).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 6).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow22ModuleRepresentation.representation PrimitiveAffineEightFrameTop13TopCertificate.ambient
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 6) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D6

namespace D7

private def displacementBasis (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1530 else 2655) else (if j.val < 3 then 20655 else 41205))

private def displacementDual (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1024 else 2048) else (if j.val < 3 then 16384 else 32768))

def displacementChart :
    BinaryCoordinateSpace 16 4 :=
  binaryCoordinateSpaceOfMasks 16 4
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 7).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 7).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1 else 4) else (if j.val < 3 then 1 else 1))

private def generatorRows (j : Fin 4) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[4] else #[4,4,4,4]) else (if j.val < 3 then #[4] else #[4]))

private def stateBasisRows (j : Fin 4) :
    Array (Fin 5) :=
  (if j.val < 2 then (if j.val < 1 then #[2] else #[0,1,2,4]) else (if j.val < 3 then #[4] else #[0]))

private def termGenerator (j : Fin 4)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 4)
    (t : Fin (termCount j)) : Fin 5 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 4)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 7).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 7).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow22ModuleRepresentation.representation PrimitiveAffineEightFrameTop13TopCertificate.ambient
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 7) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D7

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistry

end
