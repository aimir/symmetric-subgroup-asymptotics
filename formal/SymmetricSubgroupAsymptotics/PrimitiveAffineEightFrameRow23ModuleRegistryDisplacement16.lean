import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 16–26. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleRegistry

local instance sourceGroupDisplacement16 : Group Source := PrimitiveAffineEightFrameRow23TopCertificate.group
local instance sourceInhabitedDisplacement16 : Inhabited Source := ⟨1⟩

namespace D16

private def displacementBasis (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 255 else 380) else (if j.val < 3 then 564 else 1068)) else (if j.val < 6 then (if j.val < 5 then 2110 else 4151) else (if j.val < 7 then 8211 else (if j.val < 8 then 16434 else 32844))))

private def displacementDual (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 128 else 256) else (if j.val < 3 then 512 else 1024)) else (if j.val < 6 then (if j.val < 5 then 2048 else 4096) else (if j.val < 7 then 8192 else (if j.val < 8 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 9 :=
  binaryCoordinateSpaceOfMasks 16 9
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 16).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 16).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 6) else (if j.val < 3 then 5 else 6)) else (if j.val < 6 then (if j.val < 5 then 5 else 6) else (if j.val < 7 then 4 else (if j.val < 8 then 4 else 5))))

private def generatorRows (j : Fin 9) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,1,2] else #[0,0,0,1,2,2]) else (if j.val < 3 then #[0,1,1,2,2] else #[0,0,0,0,1,2])) else (if j.val < 6 then (if j.val < 5 then #[0,0,1,1,2] else #[0,0,0,1,2,2]) else (if j.val < 7 then #[1,1,2,2] else (if j.val < 8 then #[0,0,1,2] else #[0,1,1,2,2]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 9) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[2,5,2] else #[2,5,6,2,1,2]) else (if j.val < 3 then #[1,1,5,1,2] else #[1,2,5,6,5,1])) else (if j.val < 6 then (if j.val < 5 then #[1,2,1,2,1] else #[2,5,6,5,1,2]) else (if j.val < 7 then #[2,5,1,2] else (if j.val < 8 then #[2,6,2,1] else #[6,2,5,1,2]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 9 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 16).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 16).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 16) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D16

namespace D17

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 5 else 10) else (if j.val < 3 then 80 else (if j.val < 4 then 160 else 1280))) else (if j.val < 7 then (if j.val < 6 then 2560 else 4369) else (if j.val < 8 then 8738 else (if j.val < 9 then 16657 else 33314))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 4 else 8) else (if j.val < 3 then 64 else (if j.val < 4 then 128 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 17).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 17).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 4 else 6) else (if j.val < 3 then 5 else (if j.val < 4 then 8 else 7))) else (if j.val < 7 then (if j.val < 6 then 5 else 3) else (if j.val < 8 then 8 else (if j.val < 9 then 4 else 4))))

private def generatorRows (j : Fin 10) :
    Array (Fin 3) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1,1,2] else #[0,1,1,1,1,2]) else (if j.val < 3 then #[0,0,1,1,2] else (if j.val < 4 then #[0,1,1,1,1,1,1,2] else #[0,1,1,1,1,1,2]))) else (if j.val < 7 then (if j.val < 6 then #[0,1,1,1,2] else #[1,1,2]) else (if j.val < 8 then #[0,0,1,1,1,1,2,2] else (if j.val < 9 then #[0,1,2,2] else #[1,1,1,2]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[6,1,2,1] else #[7,0,2,6,7,1]) else (if j.val < 3 then #[6,7,0,4,1] else (if j.val < 4 then #[7,0,1,2,4,6,7,1] else #[7,0,1,2,6,7,1]))) else (if j.val < 7 then (if j.val < 6 then #[6,0,1,2,1] else #[6,7,7]) else (if j.val < 8 then #[6,7,0,1,2,7,1,7] else (if j.val < 9 then #[6,4,1,7] else #[1,4,7,7]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 17).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 17).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 17) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D17

namespace D18

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 291 else (if j.val < 4 then 561 else 1062))) else (if j.val < 7 then (if j.val < 6 then 2107 else 4157) else (if j.val < 8 then 8214 else (if j.val < 9 then 16440 else 32796))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 256 else (if j.val < 4 then 512 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 18).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 18).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 6 else 7) else (if j.val < 3 then 3 else (if j.val < 4 then 3 else 5))) else (if j.val < 7 then (if j.val < 6 then 5 else 5) else (if j.val < 8 then 7 else (if j.val < 9 then 7 else 4))))

private def generatorRows (j : Fin 10) :
    Array (Fin 3) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0,0,1,1,2] else #[0,0,0,1,1,1,2]) else (if j.val < 3 then #[1,2,2] else (if j.val < 4 then #[1,1,2] else #[0,0,1,1,2]))) else (if j.val < 7 then (if j.val < 6 then #[0,1,1,1,2] else #[0,0,1,2,2]) else (if j.val < 8 then #[0,0,1,1,1,2,2] else (if j.val < 9 then #[0,0,0,1,1,2,2] else #[0,0,1,2]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 10) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[2,3,6,3,6,3] else #[2,6,7,0,3,6,3]) else (if j.val < 3 then #[3,2,3] else (if j.val < 4 then #[2,3,2] else #[6,7,0,6,2]))) else (if j.val < 7 then (if j.val < 6 then #[7,0,2,3,2] else #[2,3,6,2,3]) else (if j.val < 8 then #[2,6,0,3,6,2,3] else (if j.val < 9 then #[2,6,7,0,6,2,3] else #[3,7,0,2]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 18).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 18).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 18) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D18

namespace D19

private def displacementBasis (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 255 else 380) else (if j.val < 3 then 564 else 1068)) else (if j.val < 6 then (if j.val < 5 then 2110 else 4151) else (if j.val < 7 then 8211 else (if j.val < 8 then 16434 else 32844))))

private def displacementDual (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 128 else 256) else (if j.val < 3 then 512 else 1024)) else (if j.val < 6 then (if j.val < 5 then 2048 else 4096) else (if j.val < 7 then 8192 else (if j.val < 8 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 9 :=
  binaryCoordinateSpaceOfMasks 16 9
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 19).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 19).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 3 else 4) else (if j.val < 3 then 6 else 4)) else (if j.val < 6 then (if j.val < 5 then 6 else 4) else (if j.val < 7 then 2 else (if j.val < 8 then 4 else 3))))

private def generatorRows (j : Fin 9) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,1] else #[0,0,1,2]) else (if j.val < 3 then #[0,0,1,1,1,2] else #[0,1,1,2])) else (if j.val < 6 then (if j.val < 5 then #[0,0,0,1,1,2] else #[0,0,1,2]) else (if j.val < 7 then #[0,2] else (if j.val < 8 then #[0,1,1,2] else #[0,0,2]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[3,7,0] else #[3,7,6,2]) else (if j.val < 3 then #[2,6,0,2,3,2] else #[2,0,6,2])) else (if j.val < 6 then (if j.val < 5 then #[2,6,7,2,3,2] else #[3,7,3,2]) else (if j.val < 7 then #[6,2] else (if j.val < 8 then #[6,0,3,2] else #[6,7,2]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 19).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 19).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 19) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D19

namespace D20

private def displacementBasis (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 85 else 170) else (if j.val < 3 then 801 else 1285)) else (if j.val < 6 then (if j.val < 5 then 2347 else 4379) else (if j.val < 7 then 8460 else (if j.val < 8 then 16670 else 33030))))

private def displacementDual (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 64 else 128) else (if j.val < 3 then 512 else 1024)) else (if j.val < 6 then (if j.val < 5 then 2048 else 4096) else (if j.val < 7 then 8192 else (if j.val < 8 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 9 :=
  binaryCoordinateSpaceOfMasks 16 9
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 20).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 20).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 9) : ℕ :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 5 else 2) else (if j.val < 3 then 6 else 4)) else (if j.val < 6 then (if j.val < 5 then 4 else 6) else (if j.val < 7 then 4 else (if j.val < 8 then 5 else 6))))

private def generatorRows (j : Fin 9) :
    Array (Fin 3) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,0,1,2] else #[0,2]) else (if j.val < 3 then #[0,0,0,1,1,2] else #[0,0,0,1])) else (if j.val < 6 then (if j.val < 5 then #[0,0,0,1] else #[0,0,1,1,1,2]) else (if j.val < 7 then #[0,0,1,2] else (if j.val < 8 then #[0,0,1,1,1] else #[0,0,0,1,1,2]))))

private def stateBasisRows (j : Fin 9) :
    Array (Fin 10) :=
  (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[3,6,7,0,0] else #[6,0]) else (if j.val < 3 then #[2,3,7,0,6,0] else #[2,3,7,0])) else (if j.val < 6 then (if j.val < 5 then #[2,3,6,6] else #[3,7,0,2,3,0]) else (if j.val < 7 then #[6,7,3,0] else (if j.val < 8 then #[3,7,0,2,3] else #[3,6,7,0,3,0]))))

private def termGenerator (j : Fin 9)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 9)
    (t : Fin (termCount j)) : Fin 10 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 9)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 20).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 20).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 20) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D20

namespace D21

private def displacementBasis (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 5 else 10) else (if j.val < 3 then 80 else (if j.val < 4 then 160 else 1280))) else (if j.val < 7 then (if j.val < 6 then 2560 else 4369) else (if j.val < 8 then 8738 else (if j.val < 9 then 16657 else 33314))))

private def displacementDual (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 4 else 8) else (if j.val < 3 then 64 else (if j.val < 4 then 128 else 1024))) else (if j.val < 7 then (if j.val < 6 then 2048 else 4096) else (if j.val < 8 then 8192 else (if j.val < 9 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 10 :=
  binaryCoordinateSpaceOfMasks 16 10
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 21).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 21).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 10) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 4 else 8) else (if j.val < 3 then 3 else (if j.val < 4 then 7 else 9))) else (if j.val < 7 then (if j.val < 6 then 5 else 6) else (if j.val < 8 then 4 else (if j.val < 9 then 5 else 4))))

private def generatorRows (j : Fin 10) :
    Array (Fin 3) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1,1,2] else #[0,0,1,1,1,1,1,2]) else (if j.val < 3 then #[0,0,2] else (if j.val < 4 then #[0,1,1,1,1,1,2] else #[0,0,1,1,1,1,1,1,2]))) else (if j.val < 7 then (if j.val < 6 then #[0,1,1,1,2] else #[0,1,1,1,1,2]) else (if j.val < 8 then #[0,0,1,1] else (if j.val < 9 then #[0,1,1,1,1] else #[1,1,1,2]))))

private def stateBasisRows (j : Fin 10) :
    Array (Fin 11) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[7,1,2,1] else #[4,8,0,2,4,7,8,1]) else (if j.val < 3 then #[7,8,1] else (if j.val < 4 then #[8,1,2,4,7,8,1] else #[4,8,0,1,2,4,7,8,1]))) else (if j.val < 7 then (if j.val < 6 then #[7,0,1,2,1] else #[4,0,1,2,4,1]) else (if j.val < 8 then #[7,8,4,7] else (if j.val < 9 then #[7,1,2,7,8] else #[2,4,7,1]))))

private def termGenerator (j : Fin 10)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 10)
    (t : Fin (termCount j)) : Fin 11 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 10)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 21).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 21).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 21) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D21

namespace D22

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 10 else 80)) else (if j.val < 4 then 160 else (if j.val < 5 then 291 else 561))) else (if j.val < 9 then (if j.val < 7 then 1059 else (if j.val < 8 then 2097 else 4146)) else (if j.val < 10 then 8211 else (if j.val < 11 then 16434 else 32787))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 8 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 22).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 22).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 5 else 5)) else (if j.val < 4 then 3 else (if j.val < 5 then 3 else 3))) else (if j.val < 9 then (if j.val < 7 then 5 else (if j.val < 8 then 9 else 9)) else (if j.val < 10 then 3 else (if j.val < 11 then 5 else 3))))

private def generatorRows (j : Fin 12) :
    Array (Fin 3) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0,1,1,2] else (if j.val < 2 then #[0,0,0,1,2] else #[0,0,1,1,2])) else (if j.val < 4 then #[0,1,2] else (if j.val < 5 then #[0,1,2] else #[1,1,2]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,1,2,2] else (if j.val < 8 then #[0,0,1,1,1,1,1,2,2] else #[0,0,0,0,1,1,1,1,2])) else (if j.val < 10 then #[0,2,2] else (if j.val < 11 then #[0,1,1,2,2] else #[0,1,2]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 12) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[4,8,1,2,1] else (if j.val < 2 then #[4,8,9,1,1] else #[5,8,0,2,1])) else (if j.val < 4 then #[8,2,1] else (if j.val < 5 then #[8,8,4] else #[4,5,4]))) else (if j.val < 9 then (if j.val < 7 then #[4,9,8,1,4] else (if j.val < 8 then #[4,8,0,1,2,4,5,1,4] else #[4,5,8,9,0,1,2,5,4])) else (if j.val < 10 then #[8,1,4] else (if j.val < 11 then #[8,2,5,1,4] else #[5,0,4]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 22).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 22).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 22) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D22

namespace D23

private def displacementBasis (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 5 else 10) else (if j.val < 3 then 80 else (if j.val < 4 then 160 else 801))) else (if j.val < 8 then (if j.val < 6 then 1280 else (if j.val < 7 then 2337 else 4369)) else (if j.val < 9 then 8451 else (if j.val < 10 then 16657 else 33027))))

private def displacementDual (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 4 else 8) else (if j.val < 3 then 64 else (if j.val < 4 then 128 else 512))) else (if j.val < 8 then (if j.val < 6 then 1024 else (if j.val < 7 then 2048 else 4096)) else (if j.val < 9 then 8192 else (if j.val < 10 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 11 :=
  binaryCoordinateSpaceOfMasks 16 11
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 23).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 23).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 5 else 5) else (if j.val < 3 then 3 else (if j.val < 4 then 5 else 4))) else (if j.val < 8 then (if j.val < 6 then 6 else (if j.val < 7 then 6 else 8)) else (if j.val < 9 then 2 else (if j.val < 10 then 4 else 4))))

private def generatorRows (j : Fin 11) :
    Array (Fin 3) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0,1,1,2] else #[0,0,0,1,2]) else (if j.val < 3 then #[0,0,2] else (if j.val < 4 then #[0,0,0,1,2] else #[0,0,1,1]))) else (if j.val < 8 then (if j.val < 6 then #[0,0,0,1,1,2] else (if j.val < 7 then #[0,0,1,1,1,2] else #[0,0,1,1,1,1,1,2])) else (if j.val < 9 then #[1,1] else (if j.val < 10 then #[0,1,1,1] else #[0,0,1,2]))))

private def stateBasisRows (j : Fin 11) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[4,8,1,2,1] else #[5,8,9,0,1]) else (if j.val < 3 then #[8,9,1] else (if j.val < 4 then #[4,8,9,1,1] else #[8,9,2,8]))) else (if j.val < 8 then (if j.val < 6 then #[5,8,9,0,1,1] else (if j.val < 7 then #[4,9,0,1,8,1] else #[4,5,0,1,2,4,5,1])) else (if j.val < 9 then #[2,5] else (if j.val < 10 then #[4,1,4,5] else #[8,9,5,1]))))

private def termGenerator (j : Fin 11)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 11)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 11)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 23).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 23).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 23) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D23

namespace D24

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 10 else 80)) else (if j.val < 4 then 160 else (if j.val < 5 then 291 else 561))) else (if j.val < 9 then (if j.val < 7 then 1059 else (if j.val < 8 then 2097 else 4146)) else (if j.val < 10 then 8211 else (if j.val < 11 then 16434 else 32787))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 8 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 24).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 24).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 9 else (if j.val < 2 then 7 else 5)) else (if j.val < 4 then 6 else (if j.val < 5 then 2 else 6))) else (if j.val < 9 then (if j.val < 7 then 6 else (if j.val < 8 then 6 else 6)) else (if j.val < 10 then 3 else (if j.val < 11 then 6 else 7))))

private def generatorRows (j : Fin 12) :
    Array (Fin 3) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0,0,0,1,1,1,1,1] else (if j.val < 2 then #[0,0,0,1,1,1,1] else #[0,0,1,1,1])) else (if j.val < 4 then #[0,0,1,1,1,1] else (if j.val < 5 then #[1,2] else #[0,0,1,1,1,2]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,0,1,1,2] else (if j.val < 8 then #[0,0,1,1,1,2] else #[0,1,1,1,1,2])) else (if j.val < 10 then #[0,0,2] else (if j.val < 11 then #[0,0,1,1,1,2] else #[0,0,1,1,1,1,2]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 13) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[2,5,6,9,0,1,2,5,9] else (if j.val < 2 then #[2,5,9,1,2,5,9] else #[2,9,2,5,9])) else (if j.val < 4 then #[6,9,0,2,5,9] else (if j.val < 5 then #[5,2] else #[2,9,2,6,9,2]))) else (if j.val < 9 then (if j.val < 7 then #[2,5,9,2,9,2] else (if j.val < 8 then #[5,6,1,5,6,2] else #[5,1,5,6,9,2])) else (if j.val < 10 then #[2,10,2] else (if j.val < 11 then #[2,6,0,2,6,2] else #[6,9,0,2,5,9,2]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 13 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 24).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 24).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 24) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D24

namespace D25

private def displacementBasis (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 10 else 51)) else (if j.val < 4 then 80 else (if j.val < 5 then 147 else 272))) else (if j.val < 9 then (if j.val < 7 then 514 else (if j.val < 8 then 1040 else 2050)) else (if j.val < 11 then (if j.val < 10 then 4097 else 8211) else (if j.val < 12 then 16385 else 32787))))

private def displacementDual (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 4 else (if j.val < 2 then 8 else 32)) else (if j.val < 4 then 64 else (if j.val < 5 then 128 else 256))) else (if j.val < 9 then (if j.val < 7 then 512 else (if j.val < 8 then 1024 else 2048)) else (if j.val < 11 then (if j.val < 10 then 4096 else 8192) else (if j.val < 12 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 13 :=
  binaryCoordinateSpaceOfMasks 16 13
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 25).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 25).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 13) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 5 else (if j.val < 2 then 7 else 6)) else (if j.val < 4 then 6 else (if j.val < 5 then 6 else 6))) else (if j.val < 9 then (if j.val < 7 then 7 else (if j.val < 8 then 8 else 5)) else (if j.val < 11 then (if j.val < 10 then 3 else 6) else (if j.val < 12 then 7 else 8))))

private def generatorRows (j : Fin 13) :
    Array (Fin 3) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0,1,1,1] else (if j.val < 2 then #[0,0,0,1,1,1,1] else #[0,0,0,1,1,1])) else (if j.val < 4 then #[0,0,0,1,1,1] else (if j.val < 5 then #[0,0,0,1,1,1] else #[0,0,1,1,1,2]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,0,1,1,1,2] else (if j.val < 8 then #[0,0,0,1,1,1,1,2] else #[0,0,0,1,2])) else (if j.val < 11 then (if j.val < 10 then #[0,0,2] else #[0,0,0,1,1,2]) else (if j.val < 12 then #[0,0,0,1,1,1,2] else #[0,0,0,1,1,1,1,2]))))

private def stateBasisRows (j : Fin 13) :
    Array (Fin 14) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[3,10,3,6,10] else (if j.val < 2 then #[3,7,10,0,3,6,10] else #[2,3,7,0,6,7])) else (if j.val < 4 then #[2,3,10,3,6,10] else (if j.val < 5 then #[2,3,10,3,7,10] else #[7,10,0,7,10,2]))) else (if j.val < 9 then (if j.val < 7 then #[2,3,7,0,3,6,2] else (if j.val < 8 then #[3,6,7,0,3,6,7,2] else #[2,7,10,10,2])) else (if j.val < 11 then (if j.val < 10 then #[2,10,2] else #[2,10,11,2,10,2]) else (if j.val < 12 then #[2,3,10,3,6,10,2] else #[2,3,7,0,2,3,6,2]))))

private def termGenerator (j : Fin 13)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 13)
    (t : Fin (termCount j)) : Fin 14 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 13)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 25).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 25).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 25) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D25

namespace D26

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
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 26).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 26).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 16) : ℕ :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 9 else 6) else (if j.val < 3 then 10 else 7)) else (if j.val < 6 then (if j.val < 5 then 6 else 9) else (if j.val < 7 then 7 else 8))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 7 else 8) else (if j.val < 11 then 8 else 9)) else (if j.val < 14 then (if j.val < 13 then 11 else 6) else (if j.val < 15 then 10 else 5))))

private def generatorRows (j : Fin 16) :
    Array (Fin 3) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,0,1,1,1,1,1,1,2] else #[0,1,1,1,2,2]) else (if j.val < 3 then #[0,0,0,1,1,1,1,1,1,2] else #[0,0,1,1,1,2,2])) else (if j.val < 6 then (if j.val < 5 then #[0,1,1,1,1,2] else #[0,0,1,1,1,1,1,2,2]) else (if j.val < 7 then #[0,0,1,1,1,1,2] else #[0,1,1,1,1,1,2,2]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[0,1,1,1,1,2,2] else #[0,0,1,1,1,1,1,2]) else (if j.val < 11 then #[0,0,1,1,1,1,2,2] else #[0,0,0,1,1,1,1,1,2])) else (if j.val < 14 then (if j.val < 13 then #[0,0,0,1,1,1,1,1,1,2,2] else #[0,0,1,1,1,2]) else (if j.val < 15 then #[0,0,1,1,1,1,1,1,2,2] else #[0,1,1,1,2]))))

private def stateBasisRows (j : Fin 16) :
    Array (Fin 16) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[4,5,0,1,4,5,8,9,1] else #[4,0,4,9,0,1]) else (if j.val < 3 then #[0,4,5,0,1,4,5,8,9,1] else #[1,4,0,4,9,0,1])) else (if j.val < 6 then (if j.val < 5 then #[5,1,4,5,8,1] else #[4,5,0,1,4,8,9,0,1]) else (if j.val < 7 then #[4,5,1,4,5,8,1] else #[4,0,1,4,8,9,0,1]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[4,0,1,4,9,0,1] else #[4,5,1,4,5,8,9,1]) else (if j.val < 11 then #[4,8,0,1,4,9,0,1] else #[4,5,9,1,4,5,8,9,1])) else (if j.val < 14 then (if j.val < 13 then #[4,5,12,0,1,4,5,8,9,0,1] else #[5,13,1,5,8,1]) else (if j.val < 15 then #[4,5,0,1,4,5,8,9,0,1] else #[5,1,5,8,1]))))

private def termGenerator (j : Fin 16)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 16)
    (t : Fin (termCount j)) : Fin 16 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 16)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 26).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow23ModuleRepresentation.charts 26).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states 26) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D26

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleRegistry

end
