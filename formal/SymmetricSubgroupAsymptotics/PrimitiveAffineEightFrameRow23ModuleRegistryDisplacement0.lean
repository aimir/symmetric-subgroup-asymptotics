import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 0–15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleRegistry

local instance sourceGroupDisplacement0 : Group Source := PrimitiveAffineEightFrameRow23TopCertificate.group
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
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 0).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 0).2.mem_iff _).mpr
  exact Fin.elim0 j

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 0) displacementChart where
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
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 1).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 1).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 2) : ℕ :=
  (if j.val < 1 then 1 else 2)

private def generatorRows (j : Fin 2) :
    Array (Fin 3) :=
  (if j.val < 1 then #[2] else #[1,2])

private def stateBasisRows (j : Fin 2) :
    Array (Fin 2) :=
  (if j.val < 1 then #[1] else #[0,1])

private def termGenerator (j : Fin 2)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 2)
    (t : Fin (termCount j)) : Fin 2 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 2)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 1).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 1).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 1) displacementChart where
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
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 2).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 2).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 2) : ℕ :=
  (if j.val < 1 then 1 else 2)

private def generatorRows (j : Fin 2) :
    Array (Fin 3) :=
  (if j.val < 1 then #[1] else #[1,1])

private def stateBasisRows (j : Fin 2) :
    Array (Fin 3) :=
  (if j.val < 1 then #[0] else #[0,1])

private def termGenerator (j : Fin 2)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 2)
    (t : Fin (termCount j)) : Fin 3 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 2)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 2).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 2).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 2) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D2

namespace D3

private def displacementBasis (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1455 else 2805) else (if j.val < 3 then 20730 else 41055))

private def displacementDual (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1024 else 2048) else (if j.val < 3 then 16384 else 32768))

def displacementChart :
    BinaryCoordinateSpace 16 4 :=
  binaryCoordinateSpaceOfMasks 16 4
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 3).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 3).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 2 else 3) else (if j.val < 3 then 2 else 1))

private def generatorRows (j : Fin 4) :
    Array (Fin 3) :=
  (if j.val < 2 then (if j.val < 1 then #[1,2] else #[1,1,2]) else (if j.val < 3 then #[1,2] else #[2]))

private def stateBasisRows (j : Fin 4) :
    Array (Fin 4) :=
  (if j.val < 2 then (if j.val < 1 then #[2,0] else #[0,1,0]) else (if j.val < 3 then #[1,0] else #[0]))

private def termGenerator (j : Fin 4)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 4)
    (t : Fin (termCount j)) : Fin 4 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 4)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 3).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 3).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 3) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D3

namespace D4

private def displacementBasis (j : Fin 3) : ℕ :=
  (if j.val < 1 then 4005 else (if j.val < 2 then 21845 else 42255))

private def displacementDual (j : Fin 3) : ℕ :=
  (if j.val < 1 then 2048 else (if j.val < 2 then 16384 else 32768))

def displacementChart :
    BinaryCoordinateSpace 16 3 :=
  binaryCoordinateSpaceOfMasks 16 3
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 4).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 4).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 3) : ℕ :=
  (if j.val < 1 then 1 else (if j.val < 2 then 2 else 1))

private def generatorRows (j : Fin 3) :
    Array (Fin 3) :=
  (if j.val < 1 then #[1] else (if j.val < 2 then #[1,1] else #[1]))

private def stateBasisRows (j : Fin 3) :
    Array (Fin 4) :=
  (if j.val < 1 then #[2] else (if j.val < 2 then #[0,1] else #[1]))

private def termGenerator (j : Fin 3)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 3)
    (t : Fin (termCount j)) : Fin 4 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 3)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 4).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 4).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 4) displacementChart where
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
  (if j.val < 2 then (if j.val < 1 then 1455 else 2805) else (if j.val < 3 then 20730 else 41055))

private def displacementDual (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1024 else 2048) else (if j.val < 3 then 16384 else 32768))

def displacementChart :
    BinaryCoordinateSpace 16 4 :=
  binaryCoordinateSpaceOfMasks 16 4
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 5).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 5).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 2 else 3) else (if j.val < 3 then 3 else 1))

private def generatorRows (j : Fin 4) :
    Array (Fin 3) :=
  (if j.val < 2 then (if j.val < 1 then #[1,2] else #[1,1,2]) else (if j.val < 3 then #[1,1,2] else #[2]))

private def stateBasisRows (j : Fin 4) :
    Array (Fin 5) :=
  (if j.val < 2 then (if j.val < 1 then #[1,0] else #[1,2,0]) else (if j.val < 3 then #[0,2,0] else #[0]))

private def termGenerator (j : Fin 4)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 4)
    (t : Fin (termCount j)) : Fin 5 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 4)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 5).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 5).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 5) displacementChart where
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
  (if j.val < 2 then (if j.val < 1 then 255 else 1360) else (if j.val < 3 then 2570 else (if j.val < 4 then 20485 else 41055)))

private def displacementDual (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 128 else 1024) else (if j.val < 3 then 2048 else (if j.val < 4 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 5 :=
  binaryCoordinateSpaceOfMasks 16 5
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 6).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 6).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 2 else 4) else (if j.val < 3 then 3 else (if j.val < 4 then 1 else 4)))

private def generatorRows (j : Fin 5) :
    Array (Fin 3) :=
  (if j.val < 2 then (if j.val < 1 then #[1,1] else #[1,1,1,2]) else (if j.val < 3 then #[1,1,2] else (if j.val < 4 then #[2] else #[1,1,1,2])))

private def stateBasisRows (j : Fin 5) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[2,3] else #[1,2,3,0]) else (if j.val < 3 then #[1,2,0] else (if j.val < 4 then #[0] else #[0,1,2,0])))

private def termGenerator (j : Fin 5)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 5)
    (t : Fin (termCount j)) : Fin 6 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 5)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 6).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 6).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 6) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D6

namespace D7

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1455 else (if j.val < 2 then 2805 else 4532)) else (if j.val < 4 then 8920 else (if j.val < 5 then 16718 else 33415)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1024 else (if j.val < 2 then 2048 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 7).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 7).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 3 else (if j.val < 2 then 3 else 1)) else (if j.val < 4 then 5 else (if j.val < 5 then 5 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 3) :=
  (if j.val < 3 then (if j.val < 1 then #[1,1,1] else (if j.val < 2 then #[0,1,1] else #[2])) else (if j.val < 4 then #[0,0,1,1,2] else (if j.val < 5 then #[0,1,1,1,2] else #[1,1,2])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[0,2,3] else (if j.val < 2 then #[2,2,3] else #[3])) else (if j.val < 4 then #[2,3,0,3,3] else (if j.val < 5 then #[2,0,2,3,3] else #[0,2,3])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 6 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 7).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 7).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 7) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D7

namespace D8

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1530 else (if j.val < 2 then 2655 else 4430)) else (if j.val < 4 then 8749 else (if j.val < 5 then 16865 else 33496)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1024 else (if j.val < 2 then 2048 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 8).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 8).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 3 else (if j.val < 2 then 4 else 3)) else (if j.val < 4 then 5 else (if j.val < 5 then 1 else 4)))

private def generatorRows (j : Fin 6) :
    Array (Fin 3) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1,1] else (if j.val < 2 then #[0,1,1,1] else #[1,1,2])) else (if j.val < 4 then #[0,0,1,1,2] else (if j.val < 5 then #[2] else #[0,0,1,2])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[2,2,3] else (if j.val < 2 then #[3,0,2,3] else #[2,3,3])) else (if j.val < 4 then #[2,3,0,3,3] else (if j.val < 5 then #[3] else #[2,3,2,3])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 6 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 8).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 8).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 8) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D8

namespace D9

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1530 else (if j.val < 2 then 2655 else 4580)) else (if j.val < 4 then 8824 else (if j.val < 5 then 16715 else 33421)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1024 else (if j.val < 2 then 2048 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 9).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 9).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 3 else (if j.val < 2 then 4 else 1)) else (if j.val < 4 then 4 else (if j.val < 5 then 5 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 3) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1,1] else (if j.val < 2 then #[0,1,1,1] else #[2])) else (if j.val < 4 then #[0,1,1,2] else (if j.val < 5 then #[0,0,1,1,2] else #[0,1,2])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 6) :=
  (if j.val < 3 then (if j.val < 1 then #[3,2,3] else (if j.val < 2 then #[2,0,2,3] else #[3])) else (if j.val < 4 then #[3,0,2,3] else (if j.val < 5 then #[2,3,2,3,3] else #[2,3,3])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 6 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 9).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 9).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 9) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D9

namespace D10

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1455 else (if j.val < 2 then 2805 else 4532)) else (if j.val < 4 then 8920 else (if j.val < 5 then 16718 else 33415)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1024 else (if j.val < 2 then 2048 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 10).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 10).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 3 else 5)) else (if j.val < 4 then 3 else (if j.val < 5 then 3 else 5)))

private def generatorRows (j : Fin 6) :
    Array (Fin 3) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0,1,1,1] else (if j.val < 2 then #[0,1,1] else #[0,0,1,1,2])) else (if j.val < 4 then #[1,1,2] else (if j.val < 5 then #[0,1,2] else #[0,0,1,1,2])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[3,4,1,3,4] else (if j.val < 2 then #[3,3,4] else #[3,4,3,4,4])) else (if j.val < 4 then #[1,3,4] else (if j.val < 5 then #[3,1,4] else #[3,4,1,4,4])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 10).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 10).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 10) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D10

namespace D11

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1530 else (if j.val < 2 then 2655 else 4430)) else (if j.val < 4 then 8749 else (if j.val < 5 then 16865 else 33496)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1024 else (if j.val < 2 then 2048 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 11).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 11).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 5 else 2)) else (if j.val < 4 then 2 else (if j.val < 5 then 1 else 5)))

private def generatorRows (j : Fin 6) :
    Array (Fin 3) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1,1,1] else (if j.val < 2 then #[0,0,1,1,1] else #[1,1])) else (if j.val < 4 then #[0,1] else (if j.val < 5 then #[1] else #[0,0,0,1,1])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[3,0,3,4] else (if j.val < 2 then #[0,3,0,3,4] else #[3,4])) else (if j.val < 4 then #[0,4] else (if j.val < 5 then #[0] else #[0,3,4,0,3])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 11).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 11).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 11) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D11

namespace D12

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
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 12).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 12).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 7 else 5) else (if j.val < 3 then 5 else 7)) else (if j.val < 6 then (if j.val < 5 then 6 else 6) else (if j.val < 7 then 8 else 4)))

private def generatorRows (j : Fin 8) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,1,1,1,1,1,2] else #[1,1,1,2,2]) else (if j.val < 3 then #[1,1,1,1,2] else #[1,1,1,1,1,2,2])) else (if j.val < 6 then (if j.val < 5 then #[1,1,1,1,2,2] else #[1,1,1,1,1,2]) else (if j.val < 7 then #[1,1,1,1,1,1,2,2] else #[1,1,1,2])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,2,3,4,5,1] else #[0,2,5,0,1]) else (if j.val < 3 then #[1,2,3,4,1] else #[0,1,2,4,5,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1,2,5,0,1] else #[1,2,3,4,5,1]) else (if j.val < 7 then #[0,1,2,3,4,5,0,1] else #[1,3,4,1])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 12).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 12).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 12) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D12

namespace D13

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 1285 else 2570)) else (if j.val < 6 then (if j.val < 5 then 4379 else 8749) else (if j.val < 7 then 16670 else 33319)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 13).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 13).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 4 else 4) else (if j.val < 3 then 4 else 5)) else (if j.val < 6 then (if j.val < 5 then 4 else 3) else (if j.val < 7 then 3 else 3)))

private def generatorRows (j : Fin 8) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1,2] else #[1,1,1,2]) else (if j.val < 3 then #[0,0,1,1] else #[0,0,1,1,2])) else (if j.val < 6 then (if j.val < 5 then #[0,1,2,2] else #[1,1,2]) else (if j.val < 7 then #[0,1,2] else #[0,1,2])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[5,4,5,0] else #[0,4,5,0]) else (if j.val < 3 then #[4,5,4,5] else #[4,5,0,2,0])) else (if j.val < 6 then (if j.val < 5 then #[5,0,0,5] else #[2,5,5]) else (if j.val < 7 then #[5,0,5] else #[4,4,5])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 13).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 13).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 13) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D13

namespace D14

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 255 else (if j.val < 2 then 1360 else 2570)) else (if j.val < 5 then (if j.val < 4 then 4427 else 8743) else (if j.val < 6 then 16718 else 33400)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 128 else (if j.val < 2 then 1024 else 2048)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 14).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 14).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 5 else 4)) else (if j.val < 5 then (if j.val < 4 then 4 else 5) else (if j.val < 6 then 4 else 4)))

private def generatorRows (j : Fin 7) :
    Array (Fin 3) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0,1,1,1,1] else #[0,0,1,1])) else (if j.val < 5 then (if j.val < 4 then #[0,1,1,2] else #[0,1,1,1,2]) else (if j.val < 6 then #[0,1,1,2] else #[0,1,1,2])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[5,0] else (if j.val < 2 then #[4,0,2,4,5] else #[4,5,4,5])) else (if j.val < 5 then (if j.val < 4 then #[4,4,5,5] else #[5,0,2,4,5]) else (if j.val < 6 then #[4,0,2,5] else #[4,2,5,5])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 14).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 14).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 14) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D14

namespace D15

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 1285 else 2570)) else (if j.val < 6 then (if j.val < 5 then 4379 else 8749) else (if j.val < 7 then 16670 else 33319)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 15).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 15).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 6 else 5) else (if j.val < 3 then 6 else 4)) else (if j.val < 6 then (if j.val < 5 then 5 else 2) else (if j.val < 7 then 4 else 3)))

private def generatorRows (j : Fin 8) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,1,1,1,2] else #[1,1,1,1,2]) else (if j.val < 3 then #[0,0,0,1,1,1] else #[0,0,1,2])) else (if j.val < 6 then (if j.val < 5 then #[0,0,1,1,2] else #[0,1]) else (if j.val < 7 then #[0,0,1,1] else #[0,1,1])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 9) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[2,6,2,5,6,0] else #[0,2,5,6,0]) else (if j.val < 3 then #[2,5,6,2,5,6] else #[5,6,0,0])) else (if j.val < 6 then (if j.val < 5 then #[2,6,0,2,0] else #[2,6]) else (if j.val < 7 then #[2,6,0,2] else #[5,2,5])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 15).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 15).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 15) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D15

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleRegistry

end
