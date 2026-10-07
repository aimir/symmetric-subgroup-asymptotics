import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 0–4. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleRegistry

local instance sourceGroupDisplacement0 : Group Source := PrimitiveAffineEightFrameRow29TopCertificate.group
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
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 0).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 0).2.mem_iff _).mpr
  exact Fin.elim0 j

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow29ModuleRepresentation.representation PrimitiveAffineEightFrameRow29TopCertificate.ambient
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 0) displacementChart where
  space_le_state := displacement_le_state
  termCount := fun j ↦ Fin.elim0 j
  termGenerator := fun j ↦ Fin.elim0 j
  termVector := fun j ↦ Fin.elim0 j
  basis_eq := fun j ↦ Fin.elim0 j

end D0

namespace D1

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 87 else 412) else (if j.val < 3 then 1712 else 2594)) else (if j.val < 6 then (if j.val < 5 then 4618 else 8753) else (if j.val < 7 then 16437 else 33469)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 256) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 1).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 1).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 1 else 3)) else (if j.val < 6 then (if j.val < 5 then 3 else 1) else (if j.val < 7 then 3 else 1)))

private def generatorRows (j : Fin 8) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[1] else #[0,1,1])) else (if j.val < 6 then (if j.val < 5 then #[0,0,0] else #[0]) else (if j.val < 7 then #[0,0,0] else #[0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[2,3] else #[0]) else (if j.val < 3 then #[3] else #[2,2,3])) else (if j.val < 6 then (if j.val < 5 then #[1,2,3] else #[2]) else (if j.val < 7 then #[1,3,4] else #[5])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 1).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 1).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow29ModuleRepresentation.representation PrimitiveAffineEightFrameRow29TopCertificate.ambient
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 1) displacementChart where
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
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 169 else 589) else (if j.val < 3 then 1098 else 2356)) else (if j.val < 6 then (if j.val < 5 then 4125 else 8514) else (if j.val < 7 then 16680 else 32794)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 128 else 512) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 2).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 2).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 1) else (if j.val < 3 then 2 else 4)) else (if j.val < 6 then (if j.val < 5 then 3 else 1) else (if j.val < 7 then 3 else 5)))

private def generatorRows (j : Fin 8) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0] else #[0]) else (if j.val < 3 then #[0,1] else #[0,0,1,1])) else (if j.val < 6 then (if j.val < 5 then #[0,0,0] else #[0]) else (if j.val < 7 then #[0,0,0] else #[0,0,0,0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,2] else #[2]) else (if j.val < 3 then #[2,3] else #[2,3,2,3])) else (if j.val < 6 then (if j.val < 5 then #[0,2,3] else #[1]) else (if j.val < 7 then #[2,3,4] else #[0,1,2,3,5])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 2).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 2).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow29ModuleRepresentation.representation PrimitiveAffineEightFrameRow29TopCertificate.ambient
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 2) displacementChart where
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
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 254 else 888) else (if j.val < 3 then 1297 else 2161)) else (if j.val < 6 then (if j.val < 5 then 4387 else 8230) else (if j.val < 7 then 16747 else 33092)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 128 else 512) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 3).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 3).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1 else 1) else (if j.val < 3 then 3 else 4)) else (if j.val < 6 then (if j.val < 5 then 2 else 2) else (if j.val < 7 then 1 else 3)))

private def generatorRows (j : Fin 8) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0] else #[0]) else (if j.val < 3 then #[0,0,1] else #[0,0,1,1])) else (if j.val < 6 then (if j.val < 5 then #[0,0] else #[0,0]) else (if j.val < 7 then #[0] else #[0,0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[3] else #[0]) else (if j.val < 3 then #[2,3,3] else #[2,3,2,3])) else (if j.val < 6 then (if j.val < 5 then #[2,3] else #[1,2]) else (if j.val < 7 then #[4] else #[1,2,5])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 3).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 3).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow29ModuleRepresentation.representation PrimitiveAffineEightFrameRow29TopCertificate.ambient
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 3) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D3

namespace D4

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
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 4).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 4).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 16) : ℕ :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 4 else 2) else (if j.val < 3 then 3 else 4)) else (if j.val < 6 then (if j.val < 5 then 3 else 4) else (if j.val < 7 then 3 else 3))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 4 else 5) else (if j.val < 11 then 1 else 2)) else (if j.val < 14 then (if j.val < 13 then 5 else 6) else (if j.val < 15 then 6 else 7))))

private def generatorRows (j : Fin 16) :
    Array (Fin 3) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,1,1] else #[0,1]) else (if j.val < 3 then #[0,0,1] else #[0,0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,0,1] else #[0,0,0,1]) else (if j.val < 7 then #[0,0,1] else #[0,1,1]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[0,0,0,1] else #[0,0,0,0,1]) else (if j.val < 11 then #[1] else #[1,1])) else (if j.val < 14 then (if j.val < 13 then #[0,0,0,0,1] else #[0,0,0,0,0,1]) else (if j.val < 15 then #[0,0,0,0,0,1] else #[0,0,0,0,0,0,1]))))

private def stateBasisRows (j : Fin 16) :
    Array (Fin 16) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[6,7,0,1] else #[6,0]) else (if j.val < 3 then #[1,6,0] else #[0,1,7,1])) else (if j.val < 6 then (if j.val < 5 then #[4,7,0] else #[5,6,7,1]) else (if j.val < 7 then #[6,7,1] else #[6,0,1]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[1,2,6,0] else #[0,1,3,7,1]) else (if j.val < 11 then #[11] else #[10,11])) else (if j.val < 14 then (if j.val < 13 then #[1,2,6,8,0] else #[0,1,3,7,9,1]) else (if j.val < 15 then #[1,2,6,8,12,0] else #[0,1,3,7,9,13,1]))))

private def termGenerator (j : Fin 16)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 16)
    (t : Fin (termCount j)) : Fin 16 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 16)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 4).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 4).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow29ModuleRepresentation.representation PrimitiveAffineEightFrameRow29TopCertificate.ambient
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 4) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D4

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleRegistry

end
