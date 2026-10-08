import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 0–7. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistry

local instance sourceGroupDisplacement0 : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group
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
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 0).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 0).2.mem_iff _).mpr
  exact Fin.elim0 j

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow17ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 0) displacementChart where
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
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 1).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 1).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 2 else 1))

private def generatorRows (j : Fin 4) :
    Array (Fin 8) :=
  (if j.val < 2 then (if j.val < 1 then #[0,1] else #[1]) else (if j.val < 3 then #[0,4] else #[4]))

private def stateBasisRows (j : Fin 4) :
    Array (Fin 4) :=
  (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[2,2] else #[2]))

private def termGenerator (j : Fin 4)
    (t : Fin (termCount j)) : Fin 8 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 4)
    (t : Fin (termCount j)) : Fin 4 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 4)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 1).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 1).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow17ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 1) displacementChart where
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
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 2).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 2).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 2 else 1))

private def generatorRows (j : Fin 4) :
    Array (Fin 8) :=
  (if j.val < 2 then (if j.val < 1 then #[0,1] else #[1]) else (if j.val < 3 then #[0,4] else #[4]))

private def stateBasisRows (j : Fin 4) :
    Array (Fin 5) :=
  (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[3,3] else #[3]))

private def termGenerator (j : Fin 4)
    (t : Fin (termCount j)) : Fin 8 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 4)
    (t : Fin (termCount j)) : Fin 5 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 4)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 2).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 2).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow17ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 2) displacementChart where
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
  (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 14649 else (if j.val < 4 then 21760 else 37689)))

private def displacementDual (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 8192 else (if j.val < 4 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 5 :=
  binaryCoordinateSpaceOfMasks 16 5
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 3).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 3).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 1 else (if j.val < 4 then 2 else 2)))

private def generatorRows (j : Fin 5) :
    Array (Fin 8) :=
  (if j.val < 2 then (if j.val < 1 then #[0,1] else #[1]) else (if j.val < 3 then #[7] else (if j.val < 4 then #[0,4] else #[4,7])))

private def stateBasisRows (j : Fin 5) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[1,1] else #[1]) else (if j.val < 3 then #[0] else (if j.val < 4 then #[4,4] else #[4,0])))

private def termGenerator (j : Fin 5)
    (t : Fin (termCount j)) : Fin 8 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 5)
    (t : Fin (termCount j)) : Fin 6 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 5)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 3).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 3).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow17ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 3) displacementChart where
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
  (if j.val < 3 then (if j.val < 1 then 57 else (if j.val < 2 then 85 else 147)) else (if j.val < 4 then 14592 else (if j.val < 5 then 21760 else 37632)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 32 else (if j.val < 2 then 64 else 128)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 4).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 4).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 2 else 1)) else (if j.val < 4 then 3 else (if j.val < 5 then 3 else 4)))

private def generatorRows (j : Fin 6) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[1,7] else (if j.val < 2 then #[0,1] else #[7])) else (if j.val < 4 then #[0,1,7] else (if j.val < 5 then #[0,0,4] else #[0,1,4,7])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[1,3] else (if j.val < 2 then #[1,1] else #[3])) else (if j.val < 4 then #[3,1,3] else (if j.val < 5 then #[3,5,5] else #[3,1,5,3])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 8 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 4).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 4).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow17ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 4) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D4

namespace D5

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 27 else 45) else (if j.val < 3 then 78 else 135)) else (if j.val < 6 then (if j.val < 5 then 6912 else 11520) else (if j.val < 7 then 19968 else 34560)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else 128)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 5).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 5).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 1 else 2) else (if j.val < 7 then 3 else 2)))

private def generatorRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[0,1,1] else #[1,1])) else (if j.val < 6 then (if j.val < 5 then #[4] else #[0,4]) else (if j.val < 7 then #[0,4,4] else #[4,4])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[2,1,2] else #[1,2])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[4,5]) else (if j.val < 7 then #[6,5,6] else #[5,6])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 5).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 5).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow17ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 5) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D5

namespace D6

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 57 else (if j.val < 2 then 85 else 147)) else (if j.val < 5 then (if j.val < 4 then 7710 else 10014) else (if j.val < 6 then 19230 else 36126)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 32 else (if j.val < 2 then 64 else 128)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 6).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 6).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 3 else 2)) else (if j.val < 5 then (if j.val < 4 then 1 else 2) else (if j.val < 6 then 4 else 3)))

private def generatorRows (j : Fin 7) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,0,1] else #[0,1])) else (if j.val < 5 then (if j.val < 4 then #[7] else #[0,7]) else (if j.val < 6 then #[0,0,4,7] else #[0,4,7])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,2,2] else #[0,2])) else (if j.val < 5 then (if j.val < 4 then #[0] else #[4,0]) else (if j.val < 6 then #[4,6,6,0] else #[4,6,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 8 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 6).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 6).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow17ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 6) displacementChart where
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
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 27 else 45) else (if j.val < 3 then 78 else 135)) else (if j.val < 6 then (if j.val < 5 then 6912 else 11520) else (if j.val < 7 then 19968 else 34560)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else 128)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 7).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 7).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 2 else 1) else (if j.val < 7 then 3 else 2)))

private def generatorRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[0,1,1] else #[1,1])) else (if j.val < 6 then (if j.val < 5 then #[0,4] else #[4]) else (if j.val < 7 then #[0,0,4] else #[0,4])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 9) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[2,1,2] else #[1,2])) else (if j.val < 6 then (if j.val < 5 then #[5,4] else #[4]) else (if j.val < 7 then #[5,7,7] else #[5,7])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 7).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow17ModuleRepresentation.charts 7).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow17ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states 7) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D7

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistry

end
