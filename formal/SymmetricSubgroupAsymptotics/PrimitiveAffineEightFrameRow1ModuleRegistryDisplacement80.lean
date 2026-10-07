import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 80–87. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

local instance sourceGroupDisplacement80 : Group Source := PrimitiveAffineEightFrameRow1TopCertificate.group
local instance sourceInhabitedDisplacement80 : Inhabited Source := ⟨1⟩

namespace D80

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 285 else 655) else (if j.val < 3 then 1095 else 2095)) else (if j.val < 6 then (if j.val < 5 then 4212 else 8434) else (if j.val < 7 then 16593 else 33016)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 256 else 512) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 80).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 80).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 4 else 3)) else (if j.val < 6 then (if j.val < 5 then 2 else 4) else (if j.val < 7 then 1 else 2)))

private def generatorRows (j : Fin 8) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1] else #[0,0,1]) else (if j.val < 3 then #[0,0,0,1] else #[0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1] else #[0,0,1,1]) else (if j.val < 7 then #[0] else #[0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,0,1] else #[0,1,0]) else (if j.val < 3 then #[0,1,2,0] else #[0,3,1])) else (if j.val < 6 then (if j.val < 5 then #[1,1] else #[0,1,0,1]) else (if j.val < 7 then #[7] else #[6,7])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 80).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 80).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 80) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D80

namespace D81

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 287 else 654) else (if j.val < 3 then 1103 else 2091)) else (if j.val < 6 then (if j.val < 5 then 4340 else 8370) else (if j.val < 7 then 16625 else 33000)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 256 else 512) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 81).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 81).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 4 else 3)) else (if j.val < 6 then (if j.val < 5 then 2 else 4) else (if j.val < 7 then 1 else 2)))

private def generatorRows (j : Fin 8) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1] else #[0,0,1]) else (if j.val < 3 then #[0,0,0,1] else #[0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1] else #[0,0,1,1]) else (if j.val < 7 then #[0] else #[0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,0,1] else #[0,1,0]) else (if j.val < 3 then #[0,1,2,0] else #[0,3,1])) else (if j.val < 6 then (if j.val < 5 then #[1,1] else #[0,1,0,1]) else (if j.val < 7 then #[7] else #[6,7])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 81).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 81).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 81) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D81

namespace D82

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 329 else 627) else (if j.val < 3 then 1046 else 2268)) else (if j.val < 6 then (if j.val < 5 then 4193 else 8397) else (if j.val < 7 then 16532 else 32823)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 256 else 512) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 82).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 82).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 4 else 3)) else (if j.val < 6 then (if j.val < 5 then 2 else 4) else (if j.val < 7 then 1 else 2)))

private def generatorRows (j : Fin 8) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1] else #[0,0,1]) else (if j.val < 3 then #[0,0,0,1] else #[0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1] else #[0,0,1,1]) else (if j.val < 7 then #[0] else #[0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,0,1] else #[0,1,0]) else (if j.val < 3 then #[0,1,2,0] else #[0,3,1])) else (if j.val < 6 then (if j.val < 5 then #[1,1] else #[0,1,0,1]) else (if j.val < 7 then #[7] else #[6,7])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 82).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 82).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 82) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D82

namespace D83

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 330 else 625) else (if j.val < 3 then 1050 else 2260)) else (if j.val < 6 then (if j.val < 5 then 4257 else 8269) else (if j.val < 7 then 16548 else 32791)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 256 else 512) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 83).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 83).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 4 else 3)) else (if j.val < 6 then (if j.val < 5 then 2 else 4) else (if j.val < 7 then 1 else 2)))

private def generatorRows (j : Fin 8) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1] else #[0,0,1]) else (if j.val < 3 then #[0,0,0,1] else #[0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1] else #[0,0,1,1]) else (if j.val < 7 then #[0] else #[0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,0,1] else #[0,1,0]) else (if j.val < 3 then #[0,1,2,0] else #[0,3,1])) else (if j.val < 6 then (if j.val < 5 then #[1,1] else #[0,1,0,1]) else (if j.val < 7 then #[7] else #[6,7])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 83).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 83).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 83) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D83

namespace D84

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 340 else 764) else (if j.val < 3 then 1105 else 2291)) else (if j.val < 6 then (if j.val < 5 then 4117 else 8255) else (if j.val < 7 then 16453 else 32975)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 256 else 512) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 84).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 84).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 4 else 3)) else (if j.val < 6 then (if j.val < 5 then 2 else 4) else (if j.val < 7 then 1 else 2)))

private def generatorRows (j : Fin 8) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1] else #[0,0,1]) else (if j.val < 3 then #[0,0,0,1] else #[0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1] else #[0,0,1,1]) else (if j.val < 7 then #[0] else #[0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,0,1] else #[0,1,0]) else (if j.val < 3 then #[0,1,2,0] else #[0,3,1])) else (if j.val < 6 then (if j.val < 5 then #[1,1] else #[0,1,0,1]) else (if j.val < 7 then #[7] else #[6,7])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 84).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 84).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 84) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D84

namespace D85

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 424 else 596) else (if j.val < 3 then 1186 else 2129)) else (if j.val < 6 then (if j.val < 5 then 4138 else 8213) else (if j.val < 7 then 16522 else 32837)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 256 else 512) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 85).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 85).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 4 else 3)) else (if j.val < 6 then (if j.val < 5 then 2 else 4) else (if j.val < 7 then 1 else 2)))

private def generatorRows (j : Fin 8) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1] else #[0,0,1]) else (if j.val < 3 then #[0,0,0,1] else #[0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1] else #[0,0,1,1]) else (if j.val < 7 then #[0] else #[0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,0,1] else #[0,1,0]) else (if j.val < 3 then #[0,1,2,0] else #[0,3,1])) else (if j.val < 6 then (if j.val < 5 then #[1,1] else #[0,1,0,1]) else (if j.val < 7 then #[7] else #[6,7])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 85).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 85).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 85) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D85

namespace D86

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 482 else 549) else (if j.val < 3 then 1208 else 2181)) else (if j.val < 6 then (if j.val < 5 then 4235 else 8280) else (if j.val < 7 then 16430 else 32850)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 256 else 512) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 86).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 86).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 4 else 3)) else (if j.val < 6 then (if j.val < 5 then 2 else 4) else (if j.val < 7 then 1 else 2)))

private def generatorRows (j : Fin 8) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1] else #[0,0,1]) else (if j.val < 3 then #[0,0,0,1] else #[0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1] else #[0,0,1,1]) else (if j.val < 7 then #[0] else #[0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,0,1] else #[0,1,0]) else (if j.val < 3 then #[0,1,2,0] else #[0,3,1])) else (if j.val < 6 then (if j.val < 5 then #[1,1] else #[0,1,0,1]) else (if j.val < 7 then #[7] else #[6,7])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 86).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 86).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 86) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D86

namespace D87

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 483 else 550) else (if j.val < 3 then 1212 else 2185)) else (if j.val < 6 then (if j.val < 5 then 4299 else 8344) else (if j.val < 7 then 16446 else 32866)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 256 else 512) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 87).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 87).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 3) else (if j.val < 3 then 4 else 3)) else (if j.val < 6 then (if j.val < 5 then 2 else 4) else (if j.val < 7 then 1 else 2)))

private def generatorRows (j : Fin 8) :
    Array (Fin 4) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1] else #[0,0,1]) else (if j.val < 3 then #[0,0,0,1] else #[0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1] else #[0,0,1,1]) else (if j.val < 7 then #[0] else #[0,0])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,0,1] else #[0,1,0]) else (if j.val < 3 then #[0,1,2,0] else #[0,3,1])) else (if j.val < 6 then (if j.val < 5 then #[1,1] else #[0,1,0,1]) else (if j.val < 7 then #[7] else #[6,7])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 87).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 87).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 87) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D87

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

end
