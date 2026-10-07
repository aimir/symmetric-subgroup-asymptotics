import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 64–79. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistry

local instance sourceGroupDisplacement64 : Group Source := PrimitiveAffineEightFrameRow3TopCertificate.group
local instance sourceInhabitedDisplacement64 : Inhabited Source := ⟨1⟩

namespace D64

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 3880)) else (if j.val < 5 then (if j.val < 4 then 4369 else 10023) else (if j.val < 6 then 17425 else 33295)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 2048)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 64).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 64).2.mem_iff _).mpr
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
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 64).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 64).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 64) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D64

namespace D65

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 65).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 65).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 1 else 2) else (if j.val < 7 then 2 else (if j.val < 8 then 1 else 4))))

private def generatorRows (j : Fin 9) :
    Array (Fin 6) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0] else #[0,0,0])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[0,5]) else (if j.val < 7 then #[0,5] else (if j.val < 8 then #[0] else #[0,0,0,5]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,2] else #[2]) else (if j.val < 3 then #[3,4] else #[0,2,3])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[7,0]) else (if j.val < 7 then #[5,0] else (if j.val < 8 then #[9] else #[7,8,9,0]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 65).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 65).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 65) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D65

namespace D66

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 66).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 66).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 1) else (if j.val < 3 then 4 else 1)) else (if j.val < 6 then (if j.val < 5 then 1 else 2) else (if j.val < 7 then 2 else (if j.val < 8 then 3 else 4))))

private def generatorRows (j : Fin 9) :
    Array (Fin 6) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0]) else (if j.val < 3 then #[0,0,0,0] else #[0])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[0,5]) else (if j.val < 7 then #[0,0] else (if j.val < 8 then #[0,0,5] else #[0,0,0,5]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[1]) else (if j.val < 3 then #[0,1,3,4] else #[3])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[6,0]) else (if j.val < 7 then #[5,6] else (if j.val < 8 then #[6,9,0] else #[5,8,9,0]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 66).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 66).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 66) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D66

namespace D67

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 67).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 67).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 1) else (if j.val < 3 then 4 else 3)) else (if j.val < 6 then (if j.val < 5 then 1 else 2) else (if j.val < 7 then 2 else (if j.val < 8 then 3 else 4))))

private def generatorRows (j : Fin 9) :
    Array (Fin 6) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0]) else (if j.val < 3 then #[0,0,0,0] else #[0,0,0])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[0,5]) else (if j.val < 7 then #[0,0] else (if j.val < 8 then #[0,0,5] else #[0,0,0,5]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0]) else (if j.val < 3 then #[0,1,3,4] else #[0,1,3])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[5,0]) else (if j.val < 7 then #[5,6] else (if j.val < 8 then #[6,9,0] else #[6,8,9,0]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 67).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 67).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 67) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D67

namespace D68

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 68).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 68).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 3 else 2) else (if j.val < 7 then 4 else 5)))

private def generatorRows (j : Fin 8) :
    Array (Fin 6) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0,5] else #[0,5])) else (if j.val < 6 then (if j.val < 5 then #[0,5,5] else #[0,5]) else (if j.val < 7 then #[0,0,0,5] else #[0,0,0,5,5])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[2,3] else #[2]) else (if j.val < 3 then #[4,5,0] else #[4,1])) else (if j.val < 6 then (if j.val < 5 then #[4,0,1] else #[5,0]) else (if j.val < 7 then #[4,5,9,1] else #[4,8,9,0,1])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 68).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 68).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 68) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D68

namespace D69

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 69).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 69).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 3 else 2) else (if j.val < 7 then 4 else 5)))

private def generatorRows (j : Fin 8) :
    Array (Fin 6) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0,5] else #[0,5])) else (if j.val < 6 then (if j.val < 5 then #[0,5,5] else #[0,5]) else (if j.val < 7 then #[0,0,0,5] else #[0,0,0,5,5])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[2,3] else #[2]) else (if j.val < 3 then #[4,5,0] else #[4,1])) else (if j.val < 6 then (if j.val < 5 then #[4,0,1] else #[5,0]) else (if j.val < 7 then #[4,5,9,1] else #[4,8,9,0,1])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 69).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 69).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 69) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D69

namespace D70

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 70).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 70).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 3 else 2) else (if j.val < 7 then 4 else 5)))

private def generatorRows (j : Fin 8) :
    Array (Fin 6) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0,5] else #[0,5])) else (if j.val < 6 then (if j.val < 5 then #[0,5,5] else #[0,5]) else (if j.val < 7 then #[0,0,0,5] else #[0,0,0,5,5])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[2,3] else #[2]) else (if j.val < 3 then #[4,5,0] else #[4,1])) else (if j.val < 6 then (if j.val < 5 then #[4,0,1] else #[5,0]) else (if j.val < 7 then #[4,5,9,1] else #[4,8,9,0,1])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 70).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 70).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 70) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D70

namespace D71

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 71).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 71).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 4 else 2) else (if j.val < 7 then 3 else 5)))

private def generatorRows (j : Fin 8) :
    Array (Fin 6) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,0] else #[0,0])) else (if j.val < 6 then (if j.val < 5 then #[0,0,0,0] else #[0,0]) else (if j.val < 7 then #[0,0,0] else #[0,0,0,0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[0,2,3] else #[1,2])) else (if j.val < 6 then (if j.val < 5 then #[0,1,4,5] else #[0,4]) else (if j.val < 7 then #[0,5,9] else #[1,4,5,8,9])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 71).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 71).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 71) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D71

namespace D72

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 72).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 72).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 1 else 4) else (if j.val < 7 then 3 else (if j.val < 8 then 3 else 7))))

private def generatorRows (j : Fin 9) :
    Array (Fin 6) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,0] else #[0,0])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[0,0,0,5]) else (if j.val < 7 then #[0,0,5] else (if j.val < 8 then #[0,0,0] else #[0,0,0,0,0,0,5]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[0,2,3] else #[1,2])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[1,4,5,5]) else (if j.val < 7 then #[0,4,5] else (if j.val < 8 then #[0,5,9] else #[0,1,4,5,8,9,5]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 72).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 72).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 72) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D72

namespace D73

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 73).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 73).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 1 else 5) else (if j.val < 7 then 2 else (if j.val < 8 then 4 else 6))))

private def generatorRows (j : Fin 9) :
    Array (Fin 6) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,0] else #[0,0])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[0,0,0,0,5]) else (if j.val < 7 then #[0,0] else (if j.val < 8 then #[0,0,0,5] else #[0,0,0,0,0,5]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[0,2,3] else #[1,2])) else (if j.val < 6 then (if j.val < 5 then #[4] else #[0,1,4,5,4]) else (if j.val < 7 then #[1,4] else (if j.val < 8 then #[1,5,9,4] else #[0,4,5,8,9,4]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 73).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 73).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 73) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D73

namespace D74

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 74).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 74).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 1 else 4) else (if j.val < 7 then 3 else (if j.val < 8 then 5 else 6))))

private def generatorRows (j : Fin 9) :
    Array (Fin 6) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,0] else #[0,0])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[0,0,0,5]) else (if j.val < 7 then #[0,0,0] else (if j.val < 8 then #[0,0,0,0,5] else #[0,0,0,0,0,5]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[0,2,3] else #[1,2])) else (if j.val < 6 then (if j.val < 5 then #[4] else #[0,4,5,4]) else (if j.val < 7 then #[0,1,4] else (if j.val < 8 then #[0,1,5,9,4] else #[1,4,5,8,9,4]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 74).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 74).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 74) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D74

namespace D75

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 75).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 75).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 1 else 5) else (if j.val < 7 then 2 else (if j.val < 8 then 2 else 7))))

private def generatorRows (j : Fin 9) :
    Array (Fin 6) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0] else #[0,0,0])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[0,0,0,0,5]) else (if j.val < 7 then #[0,5] else (if j.val < 8 then #[0,0] else #[0,0,0,0,0,0,5]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 11) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,2] else #[2]) else (if j.val < 3 then #[3,4] else #[0,2,3])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[0,2,5,6,0]) else (if j.val < 7 then #[5,0] else (if j.val < 8 then #[6,10] else #[0,2,5,6,9,10,0]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 75).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 75).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 75) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D75

namespace D76

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 76).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 76).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 1) else (if j.val < 3 then 4 else 1)) else (if j.val < 6 then (if j.val < 5 then 1 else 5) else (if j.val < 7 then 3 else (if j.val < 8 then 5 else 5))))

private def generatorRows (j : Fin 9) :
    Array (Fin 6) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0]) else (if j.val < 3 then #[0,0,0,0] else #[0])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[0,0,0,0,5]) else (if j.val < 7 then #[0,0,0] else (if j.val < 8 then #[0,0,0,0,5] else #[0,0,0,0,5]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 11) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[1]) else (if j.val < 3 then #[0,1,3,4] else #[3])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[0,1,5,6,0]) else (if j.val < 7 then #[0,1,5] else (if j.val < 8 then #[0,1,6,10,0] else #[5,6,9,10,0]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 76).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 76).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 76) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D76

namespace D77

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
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 77).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 77).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 1) else (if j.val < 3 then 4 else 3)) else (if j.val < 6 then (if j.val < 5 then 1 else 3) else (if j.val < 7 then 3 else (if j.val < 8 then 5 else 7))))

private def generatorRows (j : Fin 9) :
    Array (Fin 6) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0]) else (if j.val < 3 then #[0,0,0,0] else #[0,0,0])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[0,0,5]) else (if j.val < 7 then #[0,0,0] else (if j.val < 8 then #[0,0,0,0,5] else #[0,0,0,0,0,0,5]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 11) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0]) else (if j.val < 3 then #[0,1,3,4] else #[0,1,3])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[5,6,0]) else (if j.val < 7 then #[0,1,5] else (if j.val < 8 then #[0,1,6,10,0] else #[0,1,5,6,9,10,0]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 77).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 77).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 77) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D77

namespace D78

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 30 else 39) else (if j.val < 3 then 75 else (if j.val < 4 then 141 else 1285))) else (if j.val < 7 then (if j.val < 6 then 2570 else 4367) else (if j.val < 8 then 8709 else (if j.val < 9 then 16650 else 33295))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else (if j.val < 4 then 128 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 78).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 78).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 2 else (if j.val < 4 then 1 else 1))) else (if j.val < 7 then (if j.val < 6 then 1 else 4) else (if j.val < 8 then 2 else (if j.val < 9 then 3 else 6))))

private def generatorRows (j : Fin 10) :
    Array (Fin 6) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0] else (if j.val < 4 then #[0] else #[5]))) else (if j.val < 7 then (if j.val < 6 then #[5] else #[0,0,5,5]) else (if j.val < 8 then #[0,5] else (if j.val < 9 then #[0,0,5] else #[0,0,0,0,5,5]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[4,5] else (if j.val < 4 then #[4] else #[0]))) else (if j.val < 7 then (if j.val < 6 then #[1] else #[6,7,0,1]) else (if j.val < 8 then #[6,0] else (if j.val < 9 then #[7,11,1] else #[6,7,10,11,0,1]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 78).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 78).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 78) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D78

namespace D79

private def displacementBasis (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 10 else 17)) else (if j.val < 5 then (if j.val < 4 then 34 else 65) else (if j.val < 6 then 130 else 257))) else (if j.val < 10 then (if j.val < 8 then 515 else (if j.val < 9 then 1025 else 2051)) else (if j.val < 12 then (if j.val < 11 then 4097 else 8195) else (if j.val < 13 then 16385 else 32771))))

private def displacementDual (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 8 else 16)) else (if j.val < 5 then (if j.val < 4 then 32 else 64) else (if j.val < 6 then 128 else 256))) else (if j.val < 10 then (if j.val < 8 then 512 else (if j.val < 9 then 1024 else 2048)) else (if j.val < 12 then (if j.val < 11 then 4096 else 8192) else (if j.val < 13 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 14 :=
  binaryCoordinateSpaceOfMasks 16 14
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 79).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 79).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 14) : ℕ :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 3 else 4)) else (if j.val < 5 then (if j.val < 4 then 4 else 1) else (if j.val < 6 then 2 else 6))) else (if j.val < 10 then (if j.val < 8 then 5 else (if j.val < 9 then 7 else 5)) else (if j.val < 12 then (if j.val < 11 then 5 else 6) else (if j.val < 13 then 4 else 4))))

private def generatorRows (j : Fin 14) :
    Array (Fin 6) :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0,0,1] else #[0,0,1,1])) else (if j.val < 5 then (if j.val < 4 then #[0,0,0,1] else #[1]) else (if j.val < 6 then #[1,1] else #[0,0,0,1,3,3]))) else (if j.val < 10 then (if j.val < 8 then #[0,0,0,1,3] else (if j.val < 9 then #[0,0,0,0,0,1,3] else #[0,0,0,1,3])) else (if j.val < 12 then (if j.val < 11 then #[0,0,0,1,3] else #[0,0,0,1,3,3]) else (if j.val < 13 then #[0,0,0,1] else #[0,0,0,1]))))

private def stateBasisRows (j : Fin 14) :
    Array (Fin 14) :=
  (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then #[5,7] else (if j.val < 2 then #[4,5,6] else #[1,4,6,7])) else (if j.val < 5 then (if j.val < 4 then #[0,1,5,7] else #[6]) else (if j.val < 6 then #[6,7] else #[4,5,7,6,6,7]))) else (if j.val < 10 then (if j.val < 8 then #[5,6,7,7,6] else (if j.val < 9 then #[4,5,6,7,8,6,6] else #[5,6,9,7,7])) else (if j.val < 12 then (if j.val < 11 then #[4,5,7,6,7] else #[5,6,7,7,6,7]) else (if j.val < 13 then #[4,5,13,6] else #[5,12,13,7]))))

private def termGenerator (j : Fin 14)
    (t : Fin (termCount j)) : Fin 6 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 14)
    (t : Fin (termCount j)) : Fin 14 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 14)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 79).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 79).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow3ModuleRepresentation.representation PrimitiveAffineEightFrameRow3TopCertificate.ambient
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 79) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D79

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleRegistry

end
