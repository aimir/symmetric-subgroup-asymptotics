import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 0–7. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ModuleRegistry

local instance sourceGroupDisplacement0 : Group Source := PrimitiveAffineEightFrameRow27TopCertificate.group
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
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 0).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 0).2.mem_iff _).mpr
  exact Fin.elim0 j

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow27ModuleRepresentation.representation PrimitiveAffineEightFrameRow27TopCertificate.ambient
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 0) displacementChart where
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
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 1).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 1).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 2) : ℕ :=
  (if j.val < 1 then 1 else 2)

private def generatorRows (j : Fin 2) :
    Array (Fin 3) :=
  (if j.val < 1 then #[1] else #[1,1])

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
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 1).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 1).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow27ModuleRepresentation.representation PrimitiveAffineEightFrameRow27TopCertificate.ambient
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 1) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D1

namespace D2

private def displacementBasis (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1455 else 6990) else (if j.val < 3 then 8823 else (if j.val < 4 then 19380 else 35037)))

private def displacementDual (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1024 else 4096) else (if j.val < 3 then 8192 else (if j.val < 4 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 5 :=
  binaryCoordinateSpaceOfMasks 16 5
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 2).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 2).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 3 else (if j.val < 4 then 1 else 3)))

private def generatorRows (j : Fin 5) :
    Array (Fin 3) :=
  (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,0,0] else (if j.val < 4 then #[1] else #[0,1,1])))

private def stateBasisRows (j : Fin 5) :
    Array (Fin 5) :=
  (if j.val < 2 then (if j.val < 1 then #[1,2] else #[2]) else (if j.val < 3 then #[0,1,2] else (if j.val < 4 then #[4] else #[2,3,4])))

private def termGenerator (j : Fin 5)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 5)
    (t : Fin (termCount j)) : Fin 5 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 5)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 2).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 2).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow27ModuleRepresentation.representation PrimitiveAffineEightFrameRow27TopCertificate.ambient
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 2) displacementChart where
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
  (if j.val < 2 then (if j.val < 1 then 2805 else 5355) else (if j.val < 3 then 10098 else (if j.val < 4 then 16830 else 34605)))

private def displacementDual (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 2048 else 4096) else (if j.val < 3 then 8192 else (if j.val < 4 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 5 :=
  binaryCoordinateSpaceOfMasks 16 5
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 3).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 3).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 2 else 3) else (if j.val < 3 then 2 else (if j.val < 4 then 4 else 3)))

private def generatorRows (j : Fin 5) :
    Array (Fin 3) :=
  (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0,0,0]) else (if j.val < 3 then #[0,0] else (if j.val < 4 then #[0,0,0,1] else #[0,1,1])))

private def stateBasisRows (j : Fin 5) :
    Array (Fin 5) :=
  (if j.val < 2 then (if j.val < 1 then #[0,1] else #[0,1,2]) else (if j.val < 3 then #[0,2] else (if j.val < 4 then #[0,1,2,4] else #[1,3,4])))

private def termGenerator (j : Fin 5)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 5)
    (t : Fin (termCount j)) : Fin 5 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 5)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 3).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 3).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow27ModuleRepresentation.representation PrimitiveAffineEightFrameRow27TopCertificate.ambient
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 3) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D3

namespace D4

private def displacementBasis (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 3930 else 4590) else (if j.val < 3 then 10023 else (if j.val < 4 then 17595 else 33495)))

private def displacementDual (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 2048 else 4096) else (if j.val < 3 then 8192 else (if j.val < 4 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 5 :=
  binaryCoordinateSpaceOfMasks 16 5
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 4).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 4).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 5) : ℕ :=
  (if j.val < 2 then (if j.val < 1 then 1 else 2) else (if j.val < 3 then 3 else (if j.val < 4 then 2 else 3)))

private def generatorRows (j : Fin 5) :
    Array (Fin 3) :=
  (if j.val < 2 then (if j.val < 1 then #[0] else #[0,0]) else (if j.val < 3 then #[0,0,0] else (if j.val < 4 then #[0,1] else #[0,1,1])))

private def stateBasisRows (j : Fin 5) :
    Array (Fin 5) :=
  (if j.val < 2 then (if j.val < 1 then #[2] else #[0,2]) else (if j.val < 3 then #[0,1,2] else (if j.val < 4 then #[1,4] else #[1,3,4])))

private def termGenerator (j : Fin 5)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 5)
    (t : Fin (termCount j)) : Fin 5 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 5)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 4).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 4).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow27ModuleRepresentation.representation PrimitiveAffineEightFrameRow27TopCertificate.ambient
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 4) displacementChart where
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
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 1285 else 2570)) else (if j.val < 6 then (if j.val < 5 then 4369 else 8738) else (if j.val < 7 then 16660 else 33320)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 5).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 5).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 2) else (if j.val < 3 then 1 else 1)) else (if j.val < 6 then (if j.val < 5 then 3 else 3) else (if j.val < 7 then 3 else 3)))

private def generatorRows (j : Fin 8) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0,0]) else (if j.val < 3 then #[0] else #[0])) else (if j.val < 6 then (if j.val < 5 then #[0,0,0] else #[0,0,0]) else (if j.val < 7 then #[0,0,1] else #[0,1,1])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[2,4] else #[3,5]) else (if j.val < 3 then #[4] else #[5])) else (if j.val < 6 then (if j.val < 5 then #[0,2,4] else #[1,3,5]) else (if j.val < 7 then #[0,1,7] else #[0,6,7])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 5).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 5).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow27ModuleRepresentation.representation PrimitiveAffineEightFrameRow27TopCertificate.ambient
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 5) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D5

namespace D6

private def displacementBasis (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 27 else 78) else (if j.val < 3 then 170 else (if j.val < 4 then 291 else 525))) else (if j.val < 8 then (if j.val < 6 then 1062 else (if j.val < 7 then 2055 else 4137)) else (if j.val < 9 then 8239 else (if j.val < 10 then 16428 else 32805))))

private def displacementDual (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 16 else 64) else (if j.val < 3 then 128 else (if j.val < 4 then 256 else 512))) else (if j.val < 8 then (if j.val < 6 then 1024 else (if j.val < 7 then 2048 else 4096)) else (if j.val < 9 then 8192 else (if j.val < 10 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 11 :=
  binaryCoordinateSpaceOfMasks 16 11
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 6).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 6).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 9 else 6) else (if j.val < 3 then 2 else (if j.val < 4 then 5 else 8))) else (if j.val < 8 then (if j.val < 6 then 6 else (if j.val < 7 then 8 else 1)) else (if j.val < 9 then 5 else (if j.val < 10 then 8 else 6))))

private def generatorRows (j : Fin 11) :
    Array (Fin 3) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0,0,0,0,0,0,0,0] else #[0,0,0,0,0,0]) else (if j.val < 3 then #[0,0] else (if j.val < 4 then #[0,0,0,0,0] else #[0,0,0,0,0,0,0,0]))) else (if j.val < 8 then (if j.val < 6 then #[0,0,0,0,0,0] else (if j.val < 7 then #[0,0,0,0,0,0,0,0] else #[0])) else (if j.val < 9 then #[0,0,0,0,0] else (if j.val < 10 then #[0,0,0,0,0,0,0,1] else #[0,0,0,0,1,1]))))

private def stateBasisRows (j : Fin 11) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1,2,3,4,5,6,7,8] else #[1,2,3,4,6,8]) else (if j.val < 3 then #[6,8] else (if j.val < 4 then #[2,3,4,6,8] else #[0,1,2,3,5,6,7,8]))) else (if j.val < 8 then (if j.val < 6 then #[0,2,4,6,7,8] else (if j.val < 7 then #[0,1,2,3,4,5,6,7] else #[0])) else (if j.val < 9 then #[0,1,3,5,7] else (if j.val < 10 then #[0,1,2,3,4,5,7,10] else #[1,2,3,4,9,10]))))

private def termGenerator (j : Fin 11)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 11)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 11)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 6).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 6).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow27ModuleRepresentation.representation PrimitiveAffineEightFrameRow27TopCertificate.ambient
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 6) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D6

namespace D7

private def displacementBasis (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 45 else 85) else (if j.val < 3 then 135 else (if j.val < 4 then 282 else 540))) else (if j.val < 8 then (if j.val < 6 then 1055 else (if j.val < 7 then 2070 else 4107)) else (if j.val < 9 then 8211 else (if j.val < 10 then 16398 else 32793))))

private def displacementDual (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 32 else 64) else (if j.val < 3 then 128 else (if j.val < 4 then 256 else 512))) else (if j.val < 8 then (if j.val < 6 then 1024 else (if j.val < 7 then 2048 else 4096)) else (if j.val < 9 then 8192 else (if j.val < 10 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 11 :=
  binaryCoordinateSpaceOfMasks 16 11
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 7).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 7).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 4 else 2) else (if j.val < 3 then 7 else (if j.val < 4 then 8 else 4))) else (if j.val < 8 then (if j.val < 6 then 8 else (if j.val < 7 then 3 else 5)) else (if j.val < 9 then 5 else (if j.val < 10 then 6 else 5))))

private def generatorRows (j : Fin 11) :
    Array (Fin 3) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0,0,0] else #[0,0]) else (if j.val < 3 then #[0,0,0,0,0,0,0] else (if j.val < 4 then #[0,0,0,0,0,0,0,0] else #[0,0,0,0]))) else (if j.val < 8 then (if j.val < 6 then #[0,0,0,0,0,0,0,0] else (if j.val < 7 then #[0,0,0] else #[0,0,0,0,0])) else (if j.val < 9 then #[0,0,0,0,0] else (if j.val < 10 then #[0,0,0,0,0,1] else #[0,0,0,1,1]))))

private def stateBasisRows (j : Fin 11) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1,3,5,7] else #[5,7]) else (if j.val < 3 then #[0,1,3,5,6,7,8] else (if j.val < 4 then #[0,1,2,4,5,6,7,8] else #[0,2,6,8]))) else (if j.val < 8 then (if j.val < 6 then #[0,1,2,3,4,5,6,8] else (if j.val < 7 then #[2,4,6] else #[0,2,4,6,8])) else (if j.val < 9 then #[0,1,3,5,7] else (if j.val < 10 then #[0,5,6,7,8,10] else #[0,6,8,9,10]))))

private def termGenerator (j : Fin 11)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 11)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 11)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 7).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow27ModuleRepresentation.charts 7).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow27ModuleRepresentation.representation PrimitiveAffineEightFrameRow27TopCertificate.ambient
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states 7) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D7

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ModuleRegistry

end
