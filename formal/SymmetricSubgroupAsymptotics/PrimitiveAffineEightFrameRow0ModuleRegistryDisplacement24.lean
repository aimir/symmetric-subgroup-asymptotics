import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 24–31. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

local instance sourceGroupDisplacement24 : Group Source := PrimitiveAffineEightFrameRow0TopCertificate.group
local instance sourceInhabitedDisplacement24 : Inhabited Source := ⟨1⟩

namespace D24

private def displacementBasis (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 7755 else 10200) else (if j.val < 3 then 19230 else 36210))

private def displacementDual (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 4096 else 8192) else (if j.val < 3 then 16384 else 32768))

def displacementChart :
    BinaryCoordinateSpace 16 4 :=
  binaryCoordinateSpaceOfMasks 16 4
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 24).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 24).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 2 else 3))

private def generatorRows (j : Fin 4) :
    Array (Fin 4) :=
  (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0] else #[0,0,0]))

private def stateBasisRows (j : Fin 4) :
    Array (Fin 5) :=
  (if j.val < 2 then (if j.val < 1 then #[0] else #[0,1]) else (if j.val < 3 then #[1,4] else #[1,3,4]))

private def termGenerator (j : Fin 4)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 4)
    (t : Fin (termCount j)) : Fin 5 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 4)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 24).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 24).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 24) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D24

namespace D25

private def displacementBasis (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 7860 else 10098) else (if j.val < 3 then 19425 else 36312))

private def displacementDual (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 4096 else 8192) else (if j.val < 3 then 16384 else 32768))

def displacementChart :
    BinaryCoordinateSpace 16 4 :=
  binaryCoordinateSpaceOfMasks 16 4
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 25).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 25).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 2 else 3))

private def generatorRows (j : Fin 4) :
    Array (Fin 4) :=
  (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0] else #[0,0,0]))

private def stateBasisRows (j : Fin 4) :
    Array (Fin 5) :=
  (if j.val < 2 then (if j.val < 1 then #[0] else #[0,1]) else (if j.val < 3 then #[1,4] else #[1,3,4]))

private def termGenerator (j : Fin 4)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 4)
    (t : Fin (termCount j)) : Fin 5 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 4)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 25).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 25).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 25) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D25

namespace D26

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
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 26).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 26).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 1 else (if j.val < 4 then 2 else 2)))

private def generatorRows (j : Fin 5) :
    Array (Fin 4) :=
  (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[3] else (if j.val < 4 then #[0,3] else #[0,0])))

private def stateBasisRows (j : Fin 5) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[2] else #[1,2]) else (if j.val < 3 then #[0] else (if j.val < 4 then #[5,0] else #[4,5])))

private def termGenerator (j : Fin 5)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 5)
    (t : Fin (termCount j)) : Fin 6 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 5)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 26).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 26).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 26) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D26

namespace D27

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
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 27).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 27).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 1 else (if j.val < 4 then 1 else 3)))

private def generatorRows (j : Fin 5) :
    Array (Fin 4) :=
  (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[3] else (if j.val < 4 then #[0] else #[0,0,3])))

private def stateBasisRows (j : Fin 5) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[2] else #[1,2]) else (if j.val < 3 then #[0] else (if j.val < 4 then #[5] else #[4,5,0])))

private def termGenerator (j : Fin 5)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 5)
    (t : Fin (termCount j)) : Fin 6 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 5)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 27).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 27).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 27) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D27

namespace D28

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
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 28).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 28).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 1 else (if j.val < 4 then 1 else 3)))

private def generatorRows (j : Fin 5) :
    Array (Fin 4) :=
  (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[3] else (if j.val < 4 then #[0] else #[0,0,3])))

private def stateBasisRows (j : Fin 5) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[2] else #[1,2]) else (if j.val < 3 then #[0] else (if j.val < 4 then #[5] else #[4,5,0])))

private def termGenerator (j : Fin 5)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 5)
    (t : Fin (termCount j)) : Fin 6 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 5)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 28).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 28).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 28) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D28

namespace D29

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
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 29).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 29).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 4) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 1 else 2))

private def generatorRows (j : Fin 4) :
    Array (Fin 4) :=
  (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0] else #[0,0]))

private def stateBasisRows (j : Fin 4) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[5] else #[4,5]))

private def termGenerator (j : Fin 4)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 4)
    (t : Fin (termCount j)) : Fin 6 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 4)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 29).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 29).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 29) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D29

namespace D30

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
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 30).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 30).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 1 else (if j.val < 4 then 2 else 2)))

private def generatorRows (j : Fin 5) :
    Array (Fin 4) :=
  (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[3] else (if j.val < 4 then #[0,3] else #[0,0])))

private def stateBasisRows (j : Fin 5) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[3] else (if j.val < 4 then #[5,3] else #[4,5])))

private def termGenerator (j : Fin 5)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 5)
    (t : Fin (termCount j)) : Fin 6 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 5)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 30).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 30).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 30) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D30

namespace D31

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
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 31).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 31).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 1 else (if j.val < 4 then 1 else 3)))

private def generatorRows (j : Fin 5) :
    Array (Fin 4) :=
  (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[3] else (if j.val < 4 then #[0] else #[0,0,3])))

private def stateBasisRows (j : Fin 5) :
    Array (Fin 6) :=
  (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[2] else (if j.val < 4 then #[5] else #[4,5,2])))

private def termGenerator (j : Fin 5)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 5)
    (t : Fin (termCount j)) : Fin 6 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 5)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 31).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 31).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 31) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D31

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

end
