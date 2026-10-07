import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 16–31. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleRegistry

local instance sourceGroupDisplacement16 : Group Source := PrimitiveAffineEightFrameRow20TopCertificate.group
local instance sourceInhabitedDisplacement16 : Inhabited Source := ⟨1⟩

namespace D16

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1530 else (if j.val < 2 then 2655 else 4529)) else (if j.val < 4 then 8914 else (if j.val < 5 then 16670 else 33319)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1024 else (if j.val < 2 then 2048 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 16).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 16).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 4)) else (if j.val < 4 then 2 else (if j.val < 5 then 2 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 3) :=
  (if j.val < 3 then (if j.val < 1 then #[1] else (if j.val < 2 then #[0,1] else #[0,1,1,1])) else (if j.val < 4 then #[1,1] else (if j.val < 5 then #[1,1] else #[1,1,1])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[2] else (if j.val < 2 then #[4,0] else #[3,0,2,4])) else (if j.val < 4 then #[3,4] else (if j.val < 5 then #[0,4] else #[0,3,4])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 16).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 16).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 16) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D16

namespace D17

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1530 else (if j.val < 2 then 2655 else 4529)) else (if j.val < 4 then 8914 else (if j.val < 5 then 16670 else 33319)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1024 else (if j.val < 2 then 2048 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 17).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 17).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 3 else 5)) else (if j.val < 4 then 6 else (if j.val < 5 then 2 else 2)))

private def generatorRows (j : Fin 6) :
    Array (Fin 3) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0,1,1] else #[0,0,1,1,1])) else (if j.val < 4 then #[0,0,1,1,1,1] else (if j.val < 5 then #[1,1] else #[1,1])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[4,1] else (if j.val < 2 then #[3,0,1] else #[3,4,0,1,4])) else (if j.val < 4 then #[3,4,0,1,3,4] else (if j.val < 5 then #[0,4] else #[3,4])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 17).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 17).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 17) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D17

namespace D18

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1530 else (if j.val < 2 then 2655 else 4529)) else (if j.val < 4 then 8914 else (if j.val < 5 then 16670 else 33319)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1024 else (if j.val < 2 then 2048 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 18).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 18).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 3 else 1)) else (if j.val < 4 then 6 else (if j.val < 5 then 2 else 2)))

private def generatorRows (j : Fin 6) :
    Array (Fin 3) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1] else (if j.val < 2 then #[0,1,1] else #[1])) else (if j.val < 4 then #[0,0,1,1,1,1] else (if j.val < 5 then #[1,1] else #[1,1])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[3,0] else (if j.val < 2 then #[3,0,1] else #[4])) else (if j.val < 4 then #[3,4,0,1,3,4] else (if j.val < 5 then #[0,4] else #[3,4])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 18).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 18).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 18) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D18

namespace D19

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1455 else (if j.val < 2 then 2805 else 4532)) else (if j.val < 4 then 8845 else (if j.val < 5 then 16718 else 33490)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1024 else (if j.val < 2 then 2048 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 19).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 19).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 4 else 5)) else (if j.val < 4 then 2 else (if j.val < 5 then 6 else 5)))

private def generatorRows (j : Fin 6) :
    Array (Fin 3) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,0,1,2] else #[0,0,1,1,2])) else (if j.val < 4 then #[1,1] else (if j.val < 5 then #[0,0,0,1,1,2] else #[0,0,0,1,2])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[0] else (if j.val < 2 then #[0,3,0,3] else #[0,4,0,4,3])) else (if j.val < 4 then #[0,4] else (if j.val < 5 then #[0,3,4,0,4,3] else #[0,3,4,4,3])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 19).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 19).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 19) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D19

namespace D20

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1455 else (if j.val < 2 then 2805 else 4382)) else (if j.val < 4 then 8920 else (if j.val < 5 then 16868 else 33415)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1024 else (if j.val < 2 then 2048 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 20).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 20).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 3 else (if j.val < 2 then 1 else 3)) else (if j.val < 4 then 4 else (if j.val < 5 then 1 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 3) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1,2] else (if j.val < 2 then #[0] else #[0,0,2])) else (if j.val < 4 then #[0,0,1,2] else (if j.val < 5 then #[1] else #[0,1,2])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[4,0,4] else (if j.val < 2 then #[0] else #[3,4,4])) else (if j.val < 4 then #[3,4,3,4] else (if j.val < 5 then #[0] else #[3,3,4])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 20).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 20).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 20) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D20

namespace D21

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1455 else (if j.val < 2 then 2805 else 4427)) else (if j.val < 4 then 8743 else (if j.val < 5 then 16817 else 33400)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1024 else (if j.val < 2 then 2048 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 21).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 21).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 2 else (if j.val < 2 then 3 else 2)) else (if j.val < 4 then 2 else (if j.val < 5 then 5 else 1)))

private def generatorRows (j : Fin 6) :
    Array (Fin 3) :=
  (if j.val < 3 then (if j.val < 1 then #[0,2] else (if j.val < 2 then #[0,0,2] else #[1,1])) else (if j.val < 4 then #[1,2] else (if j.val < 5 then #[0,0,1,1,2] else #[1])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 7) :=
  (if j.val < 3 then (if j.val < 1 then #[4,3] else (if j.val < 2 then #[0,4,3] else #[0,3])) else (if j.val < 4 then #[0,3] else (if j.val < 5 then #[3,4,0,3,3] else #[0])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 7 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 21).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 21).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 21) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D21

namespace D22

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 5 else 10) else (if j.val < 3 then 80 else 160)) else (if j.val < 6 then (if j.val < 5 then 1280 else 2560) else (if j.val < 7 then 20480 else 40960)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 4 else 8) else (if j.val < 3 then 64 else 128)) else (if j.val < 6 then (if j.val < 5 then 1024 else 2048) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 22).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 22).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 4 else 4) else (if j.val < 3 then 4 else 3)) else (if j.val < 6 then (if j.val < 5 then 1 else 2) else (if j.val < 7 then 5 else 3)))

private def generatorRows (j : Fin 8) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,1,1,2] else #[1,1,2,2]) else (if j.val < 3 then #[1,1,1,2] else #[1,1,2])) else (if j.val < 6 then (if j.val < 5 then #[1] else #[1,1]) else (if j.val < 7 then #[1,1,1,2,2] else #[1,1,2])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,2,1] else #[0,3,0,1]) else (if j.val < 3 then #[0,2,3,0] else #[1,2,1])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[4,5]) else (if j.val < 7 then #[0,1,2,0,1] else #[0,3,0])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 22).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 22).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 22) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D22

namespace D23

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
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 23).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 23).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 5) else (if j.val < 3 then 1 else 1)) else (if j.val < 6 then (if j.val < 5 then 5 else 5) else (if j.val < 7 then 4 else 8)))

private def generatorRows (j : Fin 8) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,2] else #[0,0,1,2,2]) else (if j.val < 3 then #[2] else #[2])) else (if j.val < 6 then (if j.val < 5 then #[0,1,1,1,2] else #[0,1,1,1,2]) else (if j.val < 7 then #[0,1,1,2] else #[0,0,1,1,1,1,2,2])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[5,0,5] else #[4,5,1,4,5]) else (if j.val < 3 then #[4] else #[5])) else (if j.val < 6 then (if j.val < 5 then #[4,0,1,5,4] else #[5,0,4,5,5]) else (if j.val < 7 then #[5,1,5,5] else #[4,5,0,1,4,5,4,5])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 23).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 23).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 23) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D23

namespace D24

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 1285 else 2570)) else (if j.val < 6 then (if j.val < 5 then 4372 else 8744) else (if j.val < 7 then 16657 else 33314)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 24).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 24).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 2 else 2) else (if j.val < 3 then 5 else 4)) else (if j.val < 6 then (if j.val < 5 then 1 else 2) else (if j.val < 7 then 5 else 7)))

private def generatorRows (j : Fin 8) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,2] else #[0,2]) else (if j.val < 3 then #[0,1,1,2,2] else #[0,0,1,2])) else (if j.val < 6 then (if j.val < 5 then #[1] else #[1,1]) else (if j.val < 7 then #[0,1,1,1,2] else #[0,0,1,1,1,2,2])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[4,4] else #[5,5]) else (if j.val < 3 then #[5,0,1,4,5] else #[4,5,0,4])) else (if j.val < 6 then (if j.val < 5 then #[5] else #[4,5]) else (if j.val < 7 then #[5,0,1,5,5] else #[4,5,0,4,5,4,5])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 24).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 24).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 24) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D24

namespace D25

private def displacementBasis (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1530 else (if j.val < 2 then 2655 else 4529)) else (if j.val < 4 then 8914 else (if j.val < 5 then 16670 else 33319)))

private def displacementDual (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 1024 else (if j.val < 2 then 2048 else 4096)) else (if j.val < 4 then 8192 else (if j.val < 5 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 6 :=
  binaryCoordinateSpaceOfMasks 16 6
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 25).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 25).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 6) : ℕ :=
  (if j.val < 3 then (if j.val < 1 then 3 else (if j.val < 2 then 2 else 1)) else (if j.val < 4 then 2 else (if j.val < 5 then 3 else 3)))

private def generatorRows (j : Fin 6) :
    Array (Fin 3) :=
  (if j.val < 3 then (if j.val < 1 then #[0,1,1] else (if j.val < 2 then #[0,1] else #[1])) else (if j.val < 4 then #[1,1] else (if j.val < 5 then #[1,1,1] else #[1,1,1])))

private def stateBasisRows (j : Fin 6) :
    Array (Fin 8) :=
  (if j.val < 3 then (if j.val < 1 then #[4,0,1] else (if j.val < 2 then #[5,0] else #[5])) else (if j.val < 4 then #[4,5] else (if j.val < 5 then #[0,1,5] else #[0,4,5])))

private def termGenerator (j : Fin 6)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 6)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 6)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 25).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 25).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 25) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D25

namespace D26

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 1285 else 2570)) else (if j.val < 6 then (if j.val < 5 then 4382 else 8743) else (if j.val < 7 then 16667 else 33325)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 26).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 26).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 6 else 3) else (if j.val < 3 then 4 else 4)) else (if j.val < 6 then (if j.val < 5 then 7 else 5) else (if j.val < 7 then 4 else 7)))

private def generatorRows (j : Fin 8) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,1,1,2,2] else #[0,1,2]) else (if j.val < 3 then #[0,0,1,2] else #[0,1,2,2])) else (if j.val < 6 then (if j.val < 5 then #[0,0,1,1,1,2,2] else #[0,1,1,1,2]) else (if j.val < 7 then #[0,1,1,2] else #[0,0,1,1,1,2,2])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 8) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[4,5,0,1,4,5] else #[4,0,4]) else (if j.val < 3 then #[4,5,0,5] else #[4,1,4,5])) else (if j.val < 6 then (if j.val < 5 then #[4,5,0,1,5,4,5] else #[4,0,4,5,4]) else (if j.val < 7 then #[5,0,5,5] else #[4,5,1,4,5,4,5])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 8 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 26).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 26).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 26) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D26

namespace D27

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 1285 else 2570)) else (if j.val < 6 then (if j.val < 5 then 4382 else 8743) else (if j.val < 7 then 16667 else 33325)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 27).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 27).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 7) else (if j.val < 3 then 6 else 3)) else (if j.val < 6 then (if j.val < 5 then 4 else 7) else (if j.val < 7 then 7 else 4)))

private def generatorRows (j : Fin 8) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1] else #[0,0,0,1,1,1,2]) else (if j.val < 3 then #[0,0,1,1,1,2] else #[0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,1,1,1] else #[0,0,0,1,1,1,2]) else (if j.val < 7 then #[0,0,1,1,1,1,2] else #[0,1,1,1])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 9) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[5,0,1] else #[2,5,6,0,1,2,5]) else (if j.val < 3 then #[5,6,0,1,2,5] else #[5,6,1])) else (if j.val < 6 then (if j.val < 5 then #[5,0,1,6] else #[2,5,6,0,1,6,5]) else (if j.val < 7 then #[2,6,0,1,2,6,5] else #[5,1,2,6])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 27).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 27).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 27) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D27

namespace D28

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 1285 else 2570)) else (if j.val < 6 then (if j.val < 5 then 4382 else 8743) else (if j.val < 7 then 16667 else 33325)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 28).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 28).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 4 else 2) else (if j.val < 3 then 3 else 5)) else (if j.val < 6 then (if j.val < 5 then 3 else 4) else (if j.val < 7 then 3 else 5)))

private def generatorRows (j : Fin 8) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,1,2] else #[0,1]) else (if j.val < 3 then #[1,1,2] else #[0,0,1,1,2])) else (if j.val < 6 then (if j.val < 5 then #[0,0,2] else #[0,1,1,1]) else (if j.val < 7 then #[0,1,2] else #[0,0,1,1,2])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 9) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[5,6,2,6] else #[6,0]) else (if j.val < 3 then #[1,2,6] else #[2,5,0,2,6])) else (if j.val < 6 then (if j.val < 5 then #[5,6,6] else #[6,0,2,5]) else (if j.val < 7 then #[5,1,6] else #[5,6,0,5,6])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 28).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 28).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 28) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D28

namespace D29

private def displacementBasis (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 1285 else 2570)) else (if j.val < 6 then (if j.val < 5 then 4382 else 8743) else (if j.val < 7 then 16667 else 33325)))

private def displacementDual (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 1024 else 2048)) else (if j.val < 6 then (if j.val < 5 then 4096 else 8192) else (if j.val < 7 then 16384 else 32768)))

def displacementChart :
    BinaryCoordinateSpace 16 8 :=
  binaryCoordinateSpaceOfMasks 16 8
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 29).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 29).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 8) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 4 else 3) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 6 else 4) else (if j.val < 7 then 5 else 4)))

private def generatorRows (j : Fin 8) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1,2] else #[0,1,2]) else (if j.val < 3 then #[0,1] else #[0,1,2])) else (if j.val < 6 then (if j.val < 5 then #[0,1,1,1,1,2] else #[0,1,1,2]) else (if j.val < 7 then #[0,0,1,1,1] else #[0,1,1,2])))

private def stateBasisRows (j : Fin 8) :
    Array (Fin 9) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[6,0,1,5] else #[5,0,5]) else (if j.val < 3 then #[6,0] else #[2,1,5])) else (if j.val < 6 then (if j.val < 5 then #[6,0,1,2,5,5] else #[5,0,2,5]) else (if j.val < 7 then #[5,6,0,2,5] else #[6,1,2,5])))

private def termGenerator (j : Fin 8)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 8)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 8)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 29).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 29).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 29) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D29

namespace D30

private def displacementBasis (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 306) else (if j.val < 3 then 534 else 1181)) else (if j.val < 6 then (if j.val < 5 then 2076 else 4227) else (if j.val < 7 then 8337 else (if j.val < 8 then 16428 else 32817))))

private def displacementDual (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 256) else (if j.val < 3 then 512 else 1024)) else (if j.val < 6 then (if j.val < 5 then 2048 else 4096) else (if j.val < 7 then 8192 else (if j.val < 8 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 9 :=
  binaryCoordinateSpaceOfMasks 16 9
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 30).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 30).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 7 else 7) else (if j.val < 3 then 6 else 5)) else (if j.val < 6 then (if j.val < 5 then 6 else 5) else (if j.val < 7 then 3 else (if j.val < 8 then 6 else 7))))

private def generatorRows (j : Fin 9) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,1,1,1,1,2] else #[0,0,0,0,1,1,2]) else (if j.val < 3 then #[0,0,0,0,1,2] else #[0,0,0,1,1])) else (if j.val < 6 then (if j.val < 5 then #[0,0,0,1,1,1] else #[0,0,1,1,2]) else (if j.val < 7 then #[0,0,1] else (if j.val < 8 then #[0,0,0,1,1,2] else #[0,0,0,1,1,1,2]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 9) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,2,1,2,5,6,1] else #[1,2,5,6,1,6,1]) else (if j.val < 3 then #[1,2,5,6,5,1] else #[1,5,6,2,5])) else (if j.val < 6 then (if j.val < 5 then #[2,5,6,1,2,6] else #[1,2,1,2,1]) else (if j.val < 7 then #[5,6,5] else (if j.val < 8 then #[1,2,5,1,2,1] else #[1,2,5,1,2,6,1]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 30).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 30).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 30) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D30

namespace D31

private def displacementBasis (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 170 else 312) else (if j.val < 3 then 531 else 1128)) else (if j.val < 6 then (if j.val < 5 then 2124 else 4131) else (if j.val < 7 then 8299 else (if j.val < 8 then 16422 else 32820))))

private def displacementDual (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 128 else 256) else (if j.val < 3 then 512 else 1024)) else (if j.val < 6 then (if j.val < 5 then 2048 else 4096) else (if j.val < 7 then 8192 else (if j.val < 8 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 9 :=
  binaryCoordinateSpaceOfMasks 16 9
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 31).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 31).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 7 else 2) else (if j.val < 3 then 5 else 4)) else (if j.val < 6 then (if j.val < 5 then 4 else 6) else (if j.val < 7 then 1 else (if j.val < 8 then 4 else 7))))

private def generatorRows (j : Fin 9) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,1,1,1,1,2] else #[1,1]) else (if j.val < 3 then #[0,0,0,1,2] else #[0,1,1,2])) else (if j.val < 6 then (if j.val < 5 then #[0,0,1,2] else #[0,0,0,1,1,2]) else (if j.val < 7 then #[1] else (if j.val < 8 then #[0,0,1,1] else #[0,0,0,1,1,1,2]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 9) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,2,1,2,5,6,1] else #[2,5]) else (if j.val < 3 then #[1,2,6,5,1] else #[2,1,6,1])) else (if j.val < 6 then (if j.val < 5 then #[1,6,5,1] else #[1,2,6,1,2,1]) else (if j.val < 7 then #[5] else (if j.val < 8 then #[5,6,5,6] else #[1,2,6,1,2,6,1]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 31).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 31).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 31) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D31

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleRegistry

end
