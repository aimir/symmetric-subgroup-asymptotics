import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 0–6. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistry

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
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 0).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 0).2.mem_iff _).mpr
  exact Fin.elim0 j

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow16ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 0) displacementChart where
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
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 1).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 1).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 2 else 1))

private def generatorRows (j : Fin 4) :
    Array (Fin 8) :=
  (if j.val < 2 then (if j.val < 1 then #[4] else #[0,4]) else (if j.val < 3 then #[0,1] else #[1]))

private def stateBasisRows (j : Fin 4) :
    Array (Fin 4) :=
  (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[2,2] else #[2]))

private def termGenerator (j : Fin 4)
    (t : Fin (termCount j)) : Fin 8 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 4)
    (t : Fin (termCount j)) : Fin 4 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 4)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 1).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 1).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow16ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 1) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D1

namespace D2

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
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 2).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 2).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 2 else 1) else (if j.val < 7 then 2 else 1)))

private def generatorRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[1]) else (if j.val < 3 then #[0,1,2] else #[1,2])) else (if j.val < 6 then (if j.val < 5 then #[0,1] else #[1]) else (if j.val < 7 then #[0,1] else #[1])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[2,0,0] else #[0,0])) else (if j.val < 6 then (if j.val < 5 then #[4,4] else #[4]) else (if j.val < 7 then #[6,6] else #[6])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 2).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 2).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow16ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 2) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D2

namespace D3

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
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 3).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 3).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 2 else 1) else (if j.val < 7 then 2 else 1)))

private def generatorRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[1,2] else #[0,1,2])) else (if j.val < 6 then (if j.val < 5 then #[0,1] else #[1]) else (if j.val < 7 then #[0,1] else #[1])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[1,1] else #[2,1,1])) else (if j.val < 6 then (if j.val < 5 then #[4,4] else #[4]) else (if j.val < 7 then #[6,6] else #[6])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 3).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 3).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow16ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 3) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D3

namespace D4

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 1340 else 2611)) else (if j.val < 6 then (if j.val < 5 then 4372 else 8721) else (if j.val < 7 then 16680 else 33314)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 4).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 4).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 2 else 1)) else (if j.val < 6 then (if j.val < 5 then 3 else 1) else (if j.val < 7 then 3 else 1)))

private def generatorRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[2] else #[0,2]) else (if j.val < 3 then #[0,1] else #[1])) else (if j.val < 6 then (if j.val < 5 then #[0,1,1] else #[1]) else (if j.val < 7 then #[0,1,1] else #[1])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[4] else #[0,4]) else (if j.val < 3 then #[2,2] else #[2])) else (if j.val < 6 then (if j.val < 5 then #[4,2,4] else #[4]) else (if j.val < 7 then #[6,2,6] else #[6])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 4).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 4).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow16ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 4) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D4

namespace D5

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 10 else 17)) else (if j.val < 4 then 34 else (if j.val < 5 then 65 else 130))) else (if j.val < 9 then (if j.val < 7 then 1280 else (if j.val < 8 then 2560 else 4352)) else (if j.val < 10 then 8704 else (if j.val < 11 then 16640 else 33280))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 8 else 16)) else (if j.val < 4 then 32 else (if j.val < 5 then 64 else 128))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 5).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 5).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 3 else (if j.val < 2 then 4 else 2)) else (if j.val < 4 then 3 else (if j.val < 5 then 2 else 5))) else (if j.val < 9 then (if j.val < 7 then 2 else (if j.val < 8 then 1 else 3)) else (if j.val < 10 then 1 else (if j.val < 11 then 3 else 1))))

private def generatorRows (j : Fin 12) :
    Array (Fin 8) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,1,1] else (if j.val < 2 then #[0,0,1,1] else #[0,1])) else (if j.val < 4 then #[0,0,1] else (if j.val < 5 then #[1,2] else #[0,0,0,1,2]))) else (if j.val < 9 then (if j.val < 7 then #[0,1] else (if j.val < 8 then #[1] else #[0,1,1])) else (if j.val < 10 then #[1] else (if j.val < 11 then #[0,1,1] else #[1]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 12) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[2,0,1] else (if j.val < 2 then #[0,2,0,1] else #[2,1])) else (if j.val < 4 then #[0,2,0] else (if j.val < 5 then #[0,0] else #[0,2,4,1,0]))) else (if j.val < 9 then (if j.val < 7 then #[6,6] else (if j.val < 8 then #[6] else #[8,6,8])) else (if j.val < 10 then #[8] else (if j.val < 11 then #[10,6,10] else #[10]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 8 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 5).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 5).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow16ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 5) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D5

namespace D6

private def displacementBasis (j : Fin 16) : ℕ :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 4 else 8)) else (if j.val < 6 then (if j.val < 5 then 16 else 32) else (if j.val < 7 then 64 else 128))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 256 else 512) else (if j.val < 11 then 1024 else 2048)) else (if j.val < 14 then (if j.val < 13 then 4096 else 8192) else (if j.val < 15 then 16384 else 32768))))

private def displacementDual (j : Fin 16) : ℕ :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 4 else 8)) else (if j.val < 6 then (if j.val < 5 then 16 else 32) else (if j.val < 7 then 64 else 128))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 256 else 512) else (if j.val < 11 then 1024 else 2048)) else (if j.val < 14 then (if j.val < 13 then 4096 else 8192) else (if j.val < 15 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 16 :=
  binaryCoordinateSpaceOfMasks 16 16
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 6).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 6).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 16) : ℕ :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 4) else (if j.val < 3 then 5 else 2)) else (if j.val < 6 then (if j.val < 5 then 2 else 3) else (if j.val < 7 then 6 else 7))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 2 else 1) else (if j.val < 11 then 2 else 3)) else (if j.val < 14 then (if j.val < 13 then 2 else 1) else (if j.val < 15 then 2 else 1))))

private def generatorRows (j : Fin 16) :
    Array (Fin 8) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[4] else #[0,1,1,4]) else (if j.val < 3 then #[0,0,1,1,4] else #[0,4])) else (if j.val < 6 then (if j.val < 5 then #[1,4] else #[0,1,4]) else (if j.val < 7 then #[0,0,1,1,2,4] else #[0,0,0,1,1,2,4]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[1,1] else #[1]) else (if j.val < 11 then #[0,1] else #[0,1,1])) else (if j.val < 14 then (if j.val < 13 then #[0,1] else #[1]) else (if j.val < 15 then #[0,1] else #[1]))))

private def stateBasisRows (j : Fin 16) :
    Array (Fin 16) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[4,0,1,1]) else (if j.val < 3 then #[1,4,0,1,1] else #[0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1] else #[4,0,1]) else (if j.val < 7 then #[1,4,0,1,2,1] else #[1,4,6,0,1,2,1]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[8,9] else #[8]) else (if j.val < 11 then #[9,8] else #[8,8,9])) else (if j.val < 14 then (if j.val < 13 then #[12,12] else #[12]) else (if j.val < 15 then #[14,14] else #[14]))))

private def termGenerator (j : Fin 16)
    (t : Fin (termCount j)) : Fin 8 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 16)
    (t : Fin (termCount j)) : Fin 16 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 16)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 6).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 6).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow16ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 6) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D6

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistry

end
