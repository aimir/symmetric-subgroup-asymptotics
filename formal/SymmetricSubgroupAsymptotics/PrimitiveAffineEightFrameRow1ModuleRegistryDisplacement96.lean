import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 96–103. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

local instance sourceGroupDisplacement96 : Group Source := PrimitiveAffineEightFrameRow1TopCertificate.group
local instance sourceInhabitedDisplacement96 : Inhabited Source := ⟨1⟩

namespace D96

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 2570)) else (if j.val < 5 then (if j.val < 4 then 5171 else 10023) else (if j.val < 6 then 16691 else 34605)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 2048)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 96).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 96).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 3)) else (if j.val < 5 then (if j.val < 4 then 4 else 2) else (if j.val < 6 then 6 else 5)))

private def generatorRows (j : Fin 7) :
    Array (Fin 4) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,0,3])) else (if j.val < 5 then (if j.val < 4 then #[0,0,0,3] else #[0,0]) else (if j.val < 6 then #[0,0,0,0,0,3] else #[0,0,0,0,3])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 9) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[1] else #[1,3,0])) else (if j.val < 5 then (if j.val < 4 then #[0,1,4,0] else #[1,3]) else (if j.val < 6 then #[0,1,3,4,8,0] else #[1,4,7,8,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 96).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 96).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 96) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D96

namespace D97

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 2611)) else (if j.val < 5 then (if j.val < 4 then 5140 else 10014) else (if j.val < 6 then 16660 else 34605)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 2048)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 97).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 97).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 1 else 3)) else (if j.val < 5 then (if j.val < 4 then 4 else 2) else (if j.val < 6 then 6 else 5)))

private def generatorRows (j : Fin 7) :
    Array (Fin 4) :=
  (if j.val < 3 then (if j.val < 1 then #[0,0] else (if j.val < 2 then #[0] else #[0,0,3])) else (if j.val < 5 then (if j.val < 4 then #[0,0,0,3] else #[0,0]) else (if j.val < 6 then #[0,0,0,0,0,3] else #[0,0,0,0,3])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 9) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[1] else #[0,3,0])) else (if j.val < 5 then (if j.val < 4 then #[0,1,4,0] else #[0,3]) else (if j.val < 6 then #[0,1,3,4,8,0] else #[1,4,7,8,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 97).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 97).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 97) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D97

namespace D98

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 3857)) else (if j.val < 5 then (if j.val < 4 then 4367 else 10041) else (if j.val < 6 then 17423 else 33320)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 2048)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 98).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 98).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 1 else 2)) else (if j.val < 5 then (if j.val < 4 then 4 else 3) else (if j.val < 6 then 3 else 6)))

private def generatorRows (j : Fin 7) :
    Array (Fin 4) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0] else #[0,3])) else (if j.val < 5 then (if j.val < 4 then #[0,0,0,3] else #[0,0,0]) else (if j.val < 6 then #[0,0,3] else #[0,0,0,0,0,3])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 9) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[1] else #[4,0])) else (if j.val < 5 then (if j.val < 4 then #[0,1,3,0] else #[0,1,3]) else (if j.val < 6 then #[0,8,0] else #[0,1,3,7,8,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 98).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 98).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 98) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D98

namespace D99

private def displacementBasis (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 85 else (if j.val < 2 then 170 else 3855)) else (if j.val < 5 then (if j.val < 4 then 4392 else 10014) else (if j.val < 6 then 17448 else 33297)))

private def displacementDual (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 64 else (if j.val < 2 then 128 else 2048)) else (if j.val < 5 then (if j.val < 4 then 4096 else 8192) else (if j.val < 6 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 7 :=
  binaryCoordinateSpaceOfMasks 16 7
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 99).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 99).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 1 else 4)) else (if j.val < 5 then (if j.val < 4 then 3 else 2) else (if j.val < 6 then 4 else 5)))

private def generatorRows (j : Fin 7) :
    Array (Fin 4) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0] else #[0,0,0,3])) else (if j.val < 5 then (if j.val < 4 then #[0,0,3] else #[0,0]) else (if j.val < 6 then #[0,0,0,3] else #[0,0,0,0,3])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 9) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[1] else #[0,1,4,0])) else (if j.val < 5 then (if j.val < 4 then #[0,3,0] else #[0,3]) else (if j.val < 6 then #[0,1,8,0] else #[1,3,7,8,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 99).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 99).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 99) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D99

namespace D100

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
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 100).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 100).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 7) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 1 else 3)) else (if j.val < 5 then (if j.val < 4 then 2 else 1) else (if j.val < 6 then 3 else 5)))

private def generatorRows (j : Fin 7) :
    Array (Fin 4) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0] else #[0,0,3])) else (if j.val < 5 then (if j.val < 4 then #[0,3] else #[0]) else (if j.val < 6 then #[0,0,3] else #[0,0,0,0,3])))

private def stateBasisRows (j : Fin 7) :
    Array (Fin 9) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[1] else #[0,4,0])) else (if j.val < 5 then (if j.val < 4 then #[3,0] else #[3]) else (if j.val < 6 then #[1,8,0] else #[0,3,7,8,0])))

private def termGenerator (j : Fin 7)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 7)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 7)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 100).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 100).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 100) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D100

namespace D101

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
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 101).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 101).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 2) else (if j.val < 3 then 2 else 1)) else (if j.val < 6 then (if j.val < 5 then 1 else 2) else (if j.val < 7 then 2 else (if j.val < 8 then 1 else 4))))

private def generatorRows (j : Fin 9) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,0] else #[0,0]) else (if j.val < 3 then #[0,0] else #[0])) else (if j.val < 6 then (if j.val < 5 then #[3] else #[0,3]) else (if j.val < 7 then #[0,3] else (if j.val < 8 then #[0] else #[0,0,0,3]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,2] else #[1,4]) else (if j.val < 3 then #[0,4] else #[4])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[7,0]) else (if j.val < 7 then #[5,0] else (if j.val < 8 then #[9] else #[7,8,9,0]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 101).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 101).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 101) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D101

namespace D102

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
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 102).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 102).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 1) else (if j.val < 3 then 1 else 1)) else (if j.val < 6 then (if j.val < 5 then 1 else 2) else (if j.val < 7 then 2 else (if j.val < 8 then 3 else 4))))

private def generatorRows (j : Fin 9) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,0] else #[0]) else (if j.val < 3 then #[0] else #[0])) else (if j.val < 6 then (if j.val < 5 then #[3] else #[0,3]) else (if j.val < 7 then #[0,0] else (if j.val < 8 then #[0,0,3] else #[0,0,0,3]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,2,3] else #[1]) else (if j.val < 3 then #[0] else #[3])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[6,0]) else (if j.val < 7 then #[5,6] else (if j.val < 8 then #[6,9,0] else #[5,8,9,0]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 102).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 102).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 102) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D102

namespace D103

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
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 103).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 103).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 1 else 1)) else (if j.val < 6 then (if j.val < 5 then 1 else 2) else (if j.val < 7 then 2 else (if j.val < 8 then 3 else 4))))

private def generatorRows (j : Fin 9) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,0] else #[0,0,0]) else (if j.val < 3 then #[0] else #[0])) else (if j.val < 6 then (if j.val < 5 then #[3] else #[0,3]) else (if j.val < 7 then #[0,0] else (if j.val < 8 then #[0,0,3] else #[0,0,0,3]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,2,3] else #[0,1,3]) else (if j.val < 3 then #[3] else #[0])) else (if j.val < 6 then (if j.val < 5 then #[0] else #[5,0]) else (if j.val < 7 then #[5,6] else (if j.val < 8 then #[6,9,0] else #[6,8,9,0]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 103).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 103).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 103) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D103

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

end
