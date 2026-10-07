import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 64–71. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

local instance sourceGroupDisplacement64 : Group Source := PrimitiveAffineEightFrameRow0TopCertificate.group
local instance sourceInhabitedDisplacement64 : Inhabited Source := ⟨1⟩

namespace D64

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
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 64).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 64).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 1 else 2) else (if j.val < 7 then 2 else (if j.val < 8 then 3 else 4))))

private def generatorRows (j : Fin 9) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0] else #[0,0,0])) else (if j.val < 6 then (if j.val < 5 then #[3] else #[0,3]) else (if j.val < 7 then #[0,0] else (if j.val < 8 then #[0,0,3] else #[0,0,0,3]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[1,4] else #[0,3,4])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[6,0]) else (if j.val < 7 then #[5,6] else (if j.val < 8 then #[6,9,0] else #[5,8,9,0]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 64).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 64).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 64) displacementChart where
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
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 30 else 39) else (if j.val < 3 then 75 else 141)) else (if j.val < 6 then (if j.val < 5 then 3855 else 4367) else (if j.val < 7 then 9984 else (if j.val < 8 then 17423 else 33295))))

private def displacementDual (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 16 else 32) else (if j.val < 3 then 64 else 128)) else (if j.val < 6 then (if j.val < 5 then 2048 else 4096) else (if j.val < 7 then 8192 else (if j.val < 8 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 9 :=
  binaryCoordinateSpaceOfMasks 16 9
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 65).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 65).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 1 else 2) else (if j.val < 7 then 2 else (if j.val < 8 then 3 else 4))))

private def generatorRows (j : Fin 9) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0] else #[0,0,0])) else (if j.val < 6 then (if j.val < 5 then #[3] else #[0,3]) else (if j.val < 7 then #[0,0] else (if j.val < 8 then #[0,0,3] else #[0,0,0,3]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,1]) else (if j.val < 3 then #[1,4] else #[1,3,4])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[5,0]) else (if j.val < 7 then #[5,6] else (if j.val < 8 then #[6,9,0] else #[6,8,9,0]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 65).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 65).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 65) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D65

namespace D66

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 1285 else 2570)) else (if j.val < 6 then (if j.val < 5 then 4369 else 8738) else (if j.val < 7 then 16660 else 33320)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 66).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 66).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else 2)) else (if j.val < 6 then (if j.val < 5 then 3 else 2) else (if j.val < 7 then 4 else 5)))

private def generatorRows (j : Fin 8) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,3] else #[0,3])) else (if j.val < 6 then (if j.val < 5 then #[0,3,3] else #[0,3]) else (if j.val < 7 then #[0,0,0,3] else #[0,0,0,3,3])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[3] else #[2,3]) else (if j.val < 3 then #[4,5,0] else #[4,1])) else (if j.val < 6 then (if j.val < 5 then #[4,0,1] else #[5,0]) else (if j.val < 7 then #[4,5,9,1] else #[4,8,9,0,1])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 66).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 66).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 66) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D66

namespace D67

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
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 67).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 67).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 4 else 2) else (if j.val < 7 then 3 else 5)))

private def generatorRows (j : Fin 8) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0] else #[0,0,0])) else (if j.val < 6 then (if j.val < 5 then #[0,0,0,0] else #[0,0]) else (if j.val < 7 then #[0,0,0] else #[0,0,0,0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0]) else (if j.val < 3 then #[0,3] else #[1,2,3])) else (if j.val < 6 then (if j.val < 5 then #[0,1,4,5] else #[0,4]) else (if j.val < 7 then #[0,5,9] else #[1,4,5,8,9])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 67).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 67).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 67) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D67

namespace D68

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
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 68).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 68).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 1 else 4) else (if j.val < 7 then 3 else (if j.val < 8 then 3 else 7))))

private def generatorRows (j : Fin 9) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0] else #[0,0,0])) else (if j.val < 6 then (if j.val < 5 then #[3] else #[0,0,0,3]) else (if j.val < 7 then #[0,0,3] else (if j.val < 8 then #[0,0,0] else #[0,0,0,0,0,0,3]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0]) else (if j.val < 3 then #[0,3] else #[1,2,3])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[1,4,5,5]) else (if j.val < 7 then #[0,4,5] else (if j.val < 8 then #[0,5,9] else #[0,1,4,5,8,9,5]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 68).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 68).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 68) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D68

namespace D69

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
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 69).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 69).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 1 else 5) else (if j.val < 7 then 2 else (if j.val < 8 then 4 else 6))))

private def generatorRows (j : Fin 9) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0] else #[0,0,0])) else (if j.val < 6 then (if j.val < 5 then #[3] else #[0,0,0,0,3]) else (if j.val < 7 then #[0,0] else (if j.val < 8 then #[0,0,0,3] else #[0,0,0,0,0,3]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0]) else (if j.val < 3 then #[0,3] else #[1,2,3])) else (if j.val < 6 then (if j.val < 5 then #[4] else #[0,1,4,5,4]) else (if j.val < 7 then #[1,4] else (if j.val < 8 then #[1,5,9,4] else #[0,4,5,8,9,4]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 69).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 69).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 69) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D69

namespace D70

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
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 70).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 70).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 1 else 4) else (if j.val < 7 then 3 else (if j.val < 8 then 5 else 6))))

private def generatorRows (j : Fin 9) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0] else #[0,0,0])) else (if j.val < 6 then (if j.val < 5 then #[3] else #[0,0,0,3]) else (if j.val < 7 then #[0,0,0] else (if j.val < 8 then #[0,0,0,0,3] else #[0,0,0,0,0,3]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0]) else (if j.val < 3 then #[0,3] else #[1,2,3])) else (if j.val < 6 then (if j.val < 5 then #[4] else #[0,4,5,4]) else (if j.val < 7 then #[0,1,4] else (if j.val < 8 then #[0,1,5,9,4] else #[1,4,5,8,9,4]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 70).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 70).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 70) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D70

namespace D71

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 257 else (if j.val < 4 then 514 else 1028))) else (if j.val < 7 then (if j.val < 6 then 2056 else 4112) else (if j.val < 8 then 8224 else (if j.val < 9 then 16405 else 32810))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 71).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 71).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else (if j.val < 4 then 3 else 4))) else (if j.val < 7 then (if j.val < 6 then 3 else 2) else (if j.val < 8 then 4 else (if j.val < 9 then 1 else 2))))

private def generatorRows (j : Fin 10) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,1,1] else (if j.val < 4 then #[0,0,1] else #[0,0,0,1]))) else (if j.val < 7 then (if j.val < 6 then #[0,0,1] else #[0,1]) else (if j.val < 8 then #[0,0,1,1] else (if j.val < 9 then #[0] else #[0,0]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1] else #[0,1]) else (if j.val < 3 then #[3,2,3] else (if j.val < 4 then #[2,3,2] else #[2,3,4,2]))) else (if j.val < 7 then (if j.val < 6 then #[2,5,3] else #[3,3]) else (if j.val < 8 then #[2,3,2,3] else (if j.val < 9 then #[9] else #[8,9]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 71).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow0ModuleRepresentation.charts 71).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states 71) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D71

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

end
