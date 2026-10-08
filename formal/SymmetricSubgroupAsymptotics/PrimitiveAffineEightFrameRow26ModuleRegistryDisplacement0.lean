import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 0–7. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistry

local instance sourceGroupDisplacement0 : Group Source := PrimitiveAffineEightFrameTop17TopCertificate.group
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
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 0).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 0).2.mem_iff _).mpr
  exact Fin.elim0 j

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow26ModuleRepresentation.representation PrimitiveAffineEightFrameTop17TopCertificate.ambient
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 0) displacementChart where
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
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 1).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 1).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 2) : ℕ :=
  (if j.val < 1 then 2 else 1)

private def generatorRows (j : Fin 2) :
    Array (Fin 6) :=
  (if j.val < 1 then #[4,5] else #[5])

private def stateBasisRows (j : Fin 2) :
    Array (Fin 2) :=
  (if j.val < 1 then #[0,0] else #[0])

private def termGenerator (j : Fin 2)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 2)
    (t : Fin (termCount j)) : Fin 2 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 2)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 1).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 1).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow26ModuleRepresentation.representation PrimitiveAffineEightFrameTop17TopCertificate.ambient
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 1) displacementChart where
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
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 2).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 2).2.mem_iff _).mpr
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
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 2).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 2).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow26ModuleRepresentation.representation PrimitiveAffineEightFrameTop17TopCertificate.ambient
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 2) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D2

namespace D3

private def displacementBasis (j : Fin 3) : ℕ :=
  (if j.val < 1 then 3930 else (if j.val < 2 then 21845 else 42480))

private def displacementDual (j : Fin 3) : ℕ :=
  (if j.val < 1 then 2048 else (if j.val < 2 then 16384 else 32768))

def displacementChart :
    BinaryCoordinateSpace 16 3 :=
  binaryCoordinateSpaceOfMasks 16 3
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 3).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 3).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 3) : ℕ :=
  (if j.val < 1 then 3 else (if j.val < 2 then 2 else 1))

private def generatorRows (j : Fin 3) :
    Array (Fin 6) :=
  (if j.val < 1 then #[4,4,4] else (if j.val < 2 then #[4,4] else #[4]))

private def stateBasisRows (j : Fin 3) :
    Array (Fin 4) :=
  (if j.val < 1 then #[0,1,2] else (if j.val < 2 then #[1,2] else #[2]))

private def termGenerator (j : Fin 3)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 3)
    (t : Fin (termCount j)) : Fin 4 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 3)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 3).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 3).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow26ModuleRepresentation.representation PrimitiveAffineEightFrameTop17TopCertificate.ambient
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 3) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D3

namespace D4

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
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 4).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 4).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 3 else 4) else (if j.val < 3 then 1 else 2))

private def generatorRows (j : Fin 4) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[4,4,5] else #[4,4,4,5]) else (if j.val < 3 then #[5] else #[4,5]))

private def stateBasisRows (j : Fin 4) :
    Array (Fin 4) :=
  (if j.val < 2 then (if j.val < 1 then #[0,1,1] else #[0,1,2,1]) else (if j.val < 3 then #[1] else #[0,1]))

private def termGenerator (j : Fin 4)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 4)
    (t : Fin (termCount j)) : Fin 4 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 4)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 4).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 4).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow26ModuleRepresentation.representation PrimitiveAffineEightFrameTop17TopCertificate.ambient
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 4) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D4

namespace D5

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
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 5).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 5).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 4 else 3) else (if j.val < 3 then 1 else 3))

private def generatorRows (j : Fin 4) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[4,4,4,5] else #[4,4,5]) else (if j.val < 3 then #[5] else #[4,4,5]))

private def stateBasisRows (j : Fin 4) :
    Array (Fin 5) :=
  (if j.val < 2 then (if j.val < 1 then #[0,1,2,0] else #[0,2,0]) else (if j.val < 3 then #[0] else #[0,1,0]))

private def termGenerator (j : Fin 4)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 4)
    (t : Fin (termCount j)) : Fin 5 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 4)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 5).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 5).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow26ModuleRepresentation.representation PrimitiveAffineEightFrameTop17TopCertificate.ambient
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 5) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D5

namespace D6

private def displacementBasis (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 255 else 1285) else (if j.val < 3 then 2655 else (if j.val < 4 then 20560 else 40970)))

private def displacementDual (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 128 else 1024) else (if j.val < 3 then 2048 else (if j.val < 4 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 5 :=
  binaryCoordinateSpaceOfMasks 16 5
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 6).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 6).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 2 else 3) else (if j.val < 3 then 2 else (if j.val < 4 then 4 else 1)))

private def generatorRows (j : Fin 5) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[4,4] else #[4,4,5]) else (if j.val < 3 then #[4,5] else (if j.val < 4 then #[4,4,4,5] else #[5])))

private def stateBasisRows (j : Fin 5) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[2,3] else #[0,3,1]) else (if j.val < 3 then #[0,1] else (if j.val < 4 then #[0,1,2,1] else #[1])))

private def termGenerator (j : Fin 5)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 5)
    (t : Fin (termCount j)) : Fin 6 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 5)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 6).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 6).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow26ModuleRepresentation.representation PrimitiveAffineEightFrameTop17TopCertificate.ambient
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 6) displacementChart where
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
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 5 else 10) else (if j.val < 3 then 80 else 160)) else (if j.val < 6 then (if j.val < 5 then 1280 else 2560) else (if j.val < 7 then 20480 else 40960)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 4 else 8) else (if j.val < 3 then 64 else 128)) else (if j.val < 6 then (if j.val < 5 then 1024 else 2048) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 7).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 7).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 5 else 7) else (if j.val < 3 then 7 else 5)) else (if j.val < 6 then (if j.val < 5 then 6 else 6) else (if j.val < 7 then 4 else 8)))

private def generatorRows (j : Fin 8) :
    Array (Fin 6) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[4,4,4,5,5] else #[4,4,4,4,4,4,5]) else (if j.val < 3 then #[4,4,4,4,4,5,5] else #[4,4,4,4,5])) else (if j.val < 6 then (if j.val < 5 then #[4,4,4,4,4,5] else #[4,4,4,4,5,5]) else (if j.val < 7 then #[4,4,4,5] else #[4,4,4,4,4,4,5,5])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,3,4,0,1] else #[0,1,2,3,4,5,0]) else (if j.val < 3 then #[0,1,3,4,5,0,1] else #[0,2,3,5,0])) else (if j.val < 6 then (if j.val < 5 then #[0,2,3,4,5,0] else #[0,1,3,4,0,1]) else (if j.val < 7 then #[0,2,5,0] else #[0,1,2,3,4,5,0,1])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 7).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow26ModuleRepresentation.charts 7).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow26ModuleRepresentation.representation PrimitiveAffineEightFrameTop17TopCertificate.ambient
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states 7) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D7

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistry

end
