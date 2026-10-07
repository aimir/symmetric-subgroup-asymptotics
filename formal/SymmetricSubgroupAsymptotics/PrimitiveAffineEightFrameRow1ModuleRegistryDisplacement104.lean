import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 104–111. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

local instance sourceGroupDisplacement104 : Group Source := PrimitiveAffineEightFrameRow1TopCertificate.group
local instance sourceInhabitedDisplacement104 : Inhabited Source := ⟨1⟩

namespace D104

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 1285 else 2580)) else (if j.val < 6 then (if j.val < 5 then 4367 else 8764) else (if j.val < 7 then 16650 else 33320)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 104).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 104).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 5 else 3)) else (if j.val < 6 then (if j.val < 5 then 4 else 3) else (if j.val < 7 then 5 else 7)))

private def generatorRows (j : Fin 8) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0,0,0,3] else #[0,0,3])) else (if j.val < 6 then (if j.val < 5 then #[0,0,3,3] else #[0,0,3]) else (if j.val < 7 then #[0,0,0,0,3] else #[0,0,0,0,0,3,3])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0]) else (if j.val < 3 then #[0,1,4,5,0] else #[1,4,1])) else (if j.val < 6 then (if j.val < 5 then #[1,4,0,1] else #[0,5,0]) else (if j.val < 7 then #[0,4,5,9,1] else #[0,1,4,8,9,0,1])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 104).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 104).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 104) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D104

namespace D105

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 1340 else 2611)) else (if j.val < 6 then (if j.val < 5 then 4392 else 8738) else (if j.val < 7 then 16660 else 33297)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 105).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 105).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 4 else 4)) else (if j.val < 6 then (if j.val < 5 then 5 else 3) else (if j.val < 7 then 5 else 6)))

private def generatorRows (j : Fin 8) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0,0,3] else #[0,0,0,3])) else (if j.val < 6 then (if j.val < 5 then #[0,0,0,3,3] else #[0,0,3]) else (if j.val < 7 then #[0,0,0,0,3] else #[0,0,0,0,3,3])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0]) else (if j.val < 3 then #[0,4,5,0] else #[0,1,4,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1,4,0,1] else #[1,5,0]) else (if j.val < 7 then #[1,4,5,9,1] else #[0,4,8,9,0,1])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 105).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 105).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 105) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D105

namespace D106

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 1314 else 2570)) else (if j.val < 6 then (if j.val < 5 then 4369 else 8709) else (if j.val < 7 then 16691 else 33295)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 106).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 106).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 4 else 3)) else (if j.val < 6 then (if j.val < 5 then 4 else 4) else (if j.val < 7 then 6 else 6)))

private def generatorRows (j : Fin 8) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0,0,3] else #[0,0,3])) else (if j.val < 6 then (if j.val < 5 then #[0,0,3,3] else #[0,0,0,3]) else (if j.val < 7 then #[0,0,0,0,0,3] else #[0,0,0,0,3,3])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0]) else (if j.val < 3 then #[1,4,5,0] else #[0,4,1])) else (if j.val < 6 then (if j.val < 5 then #[0,4,0,1] else #[0,1,5,0]) else (if j.val < 7 then #[0,1,4,5,9,1] else #[1,4,8,9,0,1])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 106).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 106).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 106) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D106

namespace D107

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
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 107).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 107).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 2) else (if j.val < 3 then 1 else 2)) else (if j.val < 6 then (if j.val < 5 then 4 else 2) else (if j.val < 7 then 3 else 5)))

private def generatorRows (j : Fin 8) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,0] else #[0,0]) else (if j.val < 3 then #[0] else #[0,0])) else (if j.val < 6 then (if j.val < 5 then #[0,0,0,0] else #[0,0]) else (if j.val < 7 then #[0,0,0] else #[0,0,0,0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,2] else #[0,3]) else (if j.val < 3 then #[3] else #[2,3])) else (if j.val < 6 then (if j.val < 5 then #[2,3,4,5] else #[2,4]) else (if j.val < 7 then #[2,5,9] else #[3,4,5,8,9])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 107).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 107).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 107) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D107

namespace D108

private def displacementBasis (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 30 else 39) else (if j.val < 3 then 75 else 141)) else (if j.val < 6 then (if j.val < 5 then 1285 else 6917) else (if j.val < 7 then 8709 else (if j.val < 8 then 19200 else 34821))))

private def displacementDual (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else 128)) else (if j.val < 6 then (if j.val < 5 then 1024 else 4096) else (if j.val < 7 then 8192 else (if j.val < 8 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 9 :=
  binaryCoordinateSpaceOfMasks 16 9
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 108).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 108).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 2) else (if j.val < 3 then 1 else 2)) else (if j.val < 6 then (if j.val < 5 then 1 else 4) else (if j.val < 7 then 3 else (if j.val < 8 then 3 else 7))))

private def generatorRows (j : Fin 9) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,0] else #[0,0]) else (if j.val < 3 then #[0] else #[0,0])) else (if j.val < 6 then (if j.val < 5 then #[3] else #[0,0,0,3]) else (if j.val < 7 then #[0,0,3] else (if j.val < 8 then #[0,0,0] else #[0,0,0,0,0,0,3]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,2] else #[0,3]) else (if j.val < 3 then #[3] else #[2,3])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[3,4,5,5]) else (if j.val < 7 then #[2,4,5] else (if j.val < 8 then #[2,5,9] else #[2,3,4,5,8,9,5]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 108).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 108).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 108) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D108

namespace D109

private def displacementBasis (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 30 else 39) else (if j.val < 3 then 75 else 141)) else (if j.val < 6 then (if j.val < 5 then 3855 else 4367) else (if j.val < 7 then 9984 else (if j.val < 8 then 17423 else 33295))))

private def displacementDual (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else 128)) else (if j.val < 6 then (if j.val < 5 then 2048 else 4096) else (if j.val < 7 then 8192 else (if j.val < 8 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 9 :=
  binaryCoordinateSpaceOfMasks 16 9
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 109).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 109).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 2) else (if j.val < 3 then 1 else 2)) else (if j.val < 6 then (if j.val < 5 then 1 else 5) else (if j.val < 7 then 2 else (if j.val < 8 then 4 else 6))))

private def generatorRows (j : Fin 9) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,0] else #[0,0]) else (if j.val < 3 then #[0] else #[0,0])) else (if j.val < 6 then (if j.val < 5 then #[3] else #[0,0,0,0,3]) else (if j.val < 7 then #[0,0] else (if j.val < 8 then #[0,0,0,3] else #[0,0,0,0,0,3]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,2] else #[0,3]) else (if j.val < 3 then #[3] else #[2,3])) else (if j.val < 6 then (if j.val < 5 then #[4] else #[2,3,4,5,4]) else (if j.val < 7 then #[3,4] else (if j.val < 8 then #[3,5,9,4] else #[2,4,5,8,9,4]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 109).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 109).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 109) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D109

namespace D110

private def displacementBasis (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 30 else 39) else (if j.val < 3 then 75 else 141)) else (if j.val < 6 then (if j.val < 5 then 2570 else 5130) else (if j.val < 7 then 9984 else (if j.val < 8 then 16650 else 34570))))

private def displacementDual (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else 128)) else (if j.val < 6 then (if j.val < 5 then 2048 else 4096) else (if j.val < 7 then 8192 else (if j.val < 8 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 9 :=
  binaryCoordinateSpaceOfMasks 16 9
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 110).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 110).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 2) else (if j.val < 3 then 1 else 2)) else (if j.val < 6 then (if j.val < 5 then 1 else 4) else (if j.val < 7 then 3 else (if j.val < 8 then 5 else 6))))

private def generatorRows (j : Fin 9) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,0] else #[0,0]) else (if j.val < 3 then #[0] else #[0,0])) else (if j.val < 6 then (if j.val < 5 then #[3] else #[0,0,0,3]) else (if j.val < 7 then #[0,0,0] else (if j.val < 8 then #[0,0,0,0,3] else #[0,0,0,0,0,3]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,2] else #[0,3]) else (if j.val < 3 then #[3] else #[2,3])) else (if j.val < 6 then (if j.val < 5 then #[4] else #[2,4,5,4]) else (if j.val < 7 then #[2,3,4] else (if j.val < 8 then #[2,3,5,9,4] else #[3,4,5,8,9,4]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 110).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 110).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 110) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D110

namespace D111

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 257 else (if j.val < 4 then 515 else 1028))) else (if j.val < 7 then (if j.val < 6 then 2060 else 4117) else (if j.val < 8 then 8255 else (if j.val < 9 then 16400 else 32816))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 111).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 111).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 3 else (if j.val < 4 then 3 else 4))) else (if j.val < 7 then (if j.val < 6 then 3 else 4) else (if j.val < 8 then 5 else (if j.val < 9 then 1 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,1,1] else (if j.val < 4 then #[0,0,1] else #[0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,1] else #[0,0,0,1]) else (if j.val < 8 then #[0,0,0,1,1] else (if j.val < 9 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0]) else (if j.val < 3 then #[3,2,3] else (if j.val < 4 then #[2,3,2] else #[2,3,4,2]))) else (if j.val < 7 then (if j.val < 6 then #[2,5,3] else #[0,1,3,3]) else (if j.val < 8 then #[1,2,3,2,3] else (if j.val < 9 then #[9] else #[8,9]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 111).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 111).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 111) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D111

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

end
