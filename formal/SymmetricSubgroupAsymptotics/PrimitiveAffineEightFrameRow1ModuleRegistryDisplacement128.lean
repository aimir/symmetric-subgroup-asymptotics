import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 128–135. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

local instance sourceGroupDisplacement128 : Group Source := PrimitiveAffineEightFrameRow1TopCertificate.group
local instance sourceInhabitedDisplacement128 : Inhabited Source := ⟨1⟩

namespace D128

private def displacementBasis (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 54 else 85) else (if j.val < 3 then 156 else (if j.val < 4 then 258 else 513))) else (if j.val < 8 then (if j.val < 6 then 1032 else (if j.val < 7 then 2052 else 4124)) else (if j.val < 9 then 8213 else (if j.val < 10 then 16406 else 32784))))

private def displacementDual (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 32 else 64) else (if j.val < 3 then 128 else (if j.val < 4 then 256 else 512))) else (if j.val < 8 then (if j.val < 6 then 1024 else (if j.val < 7 then 2048 else 4096)) else (if j.val < 9 then 8192 else (if j.val < 10 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 11 :=
  binaryCoordinateSpaceOfMasks 16 11
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 128).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 128).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 5 else 2) else (if j.val < 3 then 4 else (if j.val < 4 then 3 else 3))) else (if j.val < 8 then (if j.val < 6 then 4 else (if j.val < 7 then 3 else 2)) else (if j.val < 9 then 6 else (if j.val < 10 then 5 else 4))))

private def generatorRows (j : Fin 11) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0,0,1,3] else #[0,0]) else (if j.val < 3 then #[0,0,1,3] else (if j.val < 4 then #[0,1,1] else #[0,0,1]))) else (if j.val < 8 then (if j.val < 6 then #[0,0,0,1] else (if j.val < 7 then #[0,0,1] else #[0,3])) else (if j.val < 9 then #[0,0,0,0,1,1] else (if j.val < 10 then #[0,0,0,1,3] else #[0,0,0,0]))))

private def stateBasisRows (j : Fin 11) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,5,7,5,0] else #[0,1]) else (if j.val < 3 then #[5,7,5,0] else (if j.val < 4 then #[5,4,5] else #[4,5,4]))) else (if j.val < 8 then (if j.val < 6 then #[4,5,6,4] else (if j.val < 7 then #[4,7,5] else #[7,0])) else (if j.val < 9 then #[0,1,4,5,4,5] else (if j.val < 10 then #[5,7,11,5,0] else #[0,1,10,11]))))

private def termGenerator (j : Fin 11)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 11)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 11)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 128).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 128).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 128) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D128

namespace D129

private def displacementBasis (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 45 else 85) else (if j.val < 3 then 135 else (if j.val < 4 then 259 else 514))) else (if j.val < 8 then (if j.val < 6 then 1036 else (if j.val < 7 then 2056 else 4114)) else (if j.val < 9 then 8199 else (if j.val < 10 then 16413 else 32781))))

private def displacementDual (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 32 else 64) else (if j.val < 3 then 128 else (if j.val < 4 then 256 else 512))) else (if j.val < 8 then (if j.val < 6 then 1024 else (if j.val < 7 then 2048 else 4096)) else (if j.val < 9 then 8192 else (if j.val < 10 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 11 :=
  binaryCoordinateSpaceOfMasks 16 11
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 129).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 129).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 5 else 2) else (if j.val < 3 then 6 else (if j.val < 4 then 3 else 3))) else (if j.val < 8 then (if j.val < 6 then 4 else (if j.val < 7 then 3 else 2)) else (if j.val < 9 then 6 else (if j.val < 10 then 5 else 8))))

private def generatorRows (j : Fin 11) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0,0,1,3] else #[0,0]) else (if j.val < 3 then #[0,0,0,0,1,3] else (if j.val < 4 then #[0,1,1] else #[0,0,1]))) else (if j.val < 8 then (if j.val < 6 then #[0,0,0,1] else (if j.val < 7 then #[0,0,1] else #[0,3])) else (if j.val < 9 then #[0,0,0,0,1,3] else (if j.val < 10 then #[0,0,0,1,3] else #[0,0,0,0,0,0,1,3]))))

private def stateBasisRows (j : Fin 11) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[1,5,7,5,0] else #[0,1]) else (if j.val < 3 then #[0,1,5,7,5,0] else (if j.val < 4 then #[5,4,5] else #[4,5,4]))) else (if j.val < 8 then (if j.val < 6 then #[4,5,6,4] else (if j.val < 7 then #[4,7,5] else #[7,0])) else (if j.val < 9 then #[0,1,4,7,4,0] else (if j.val < 10 then #[5,7,11,5,0] else #[0,1,5,7,10,11,5,0]))))

private def termGenerator (j : Fin 11)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 11)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 11)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 129).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 129).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 129) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D129

namespace D130

private def displacementBasis (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 27 else 78) else (if j.val < 3 then 170 else (if j.val < 4 then 260 else 548))) else (if j.val < 8 then (if j.val < 6 then 1025 else (if j.val < 7 then 2091 else 4107)) else (if j.val < 9 then 8195 else (if j.val < 10 then 16398 else 32780))))

private def displacementDual (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 16 else 64) else (if j.val < 3 then 128 else (if j.val < 4 then 256 else 512))) else (if j.val < 8 then (if j.val < 6 then 1024 else (if j.val < 7 then 2048 else 4096)) else (if j.val < 9 then 8192 else (if j.val < 10 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 11 :=
  binaryCoordinateSpaceOfMasks 16 11
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 130).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 130).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 7 else 9) else (if j.val < 3 then 1 else (if j.val < 4 then 5 else 4))) else (if j.val < 8 then (if j.val < 6 then 3 else (if j.val < 7 then 3 else 3)) else (if j.val < 9 then 4 else (if j.val < 10 then 1 else 11))))

private def generatorRows (j : Fin 11) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0,0,0,1,1,3] else #[0,0,0,0,0,0,1,1,3]) else (if j.val < 3 then #[0] else (if j.val < 4 then #[0,0,0,0,3] else #[0,0,0,1]))) else (if j.val < 8 then (if j.val < 6 then #[0,1,3] else (if j.val < 7 then #[0,0,1] else #[0,0,1])) else (if j.val < 9 then #[0,0,0,3] else (if j.val < 10 then #[0] else #[0,0,0,0,0,0,0,0,1,1,3]))))

private def stateBasisRows (j : Fin 11) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[4,5,6,7,4,5,1] else #[0,1,4,5,6,7,4,5,1]) else (if j.val < 3 then #[0] else (if j.val < 4 then #[0,4,6,7,1] else #[1,4,5,4]))) else (if j.val < 8 then (if j.val < 6 then #[7,5,1] else (if j.val < 7 then #[4,7,5] else #[0,5,5])) else (if j.val < 9 then #[0,6,7,1] else (if j.val < 10 then #[11] else #[0,1,4,5,6,7,10,11,4,5,1]))))

private def termGenerator (j : Fin 11)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 11)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 11)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 130).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 130).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 130) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D130

namespace D131

private def displacementBasis (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 45 else 85) else (if j.val < 3 then 135 else (if j.val < 4 then 285 else 520))) else (if j.val < 8 then (if j.val < 6 then 1042 else (if j.val < 7 then 2050 else 4108)) else (if j.val < 9 then 8205 else (if j.val < 10 then 16387 else 32775))))

private def displacementDual (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 32 else 64) else (if j.val < 3 then 128 else (if j.val < 4 then 256 else 512))) else (if j.val < 8 then (if j.val < 6 then 1024 else (if j.val < 7 then 2048 else 4096)) else (if j.val < 9 then 8192 else (if j.val < 10 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 11 :=
  binaryCoordinateSpaceOfMasks 16 11
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 131).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 131).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 6 else 2) else (if j.val < 3 then 5 else (if j.val < 4 then 4 else 6))) else (if j.val < 8 then (if j.val < 6 then 4 else (if j.val < 7 then 5 else 4)) else (if j.val < 9 then 5 else (if j.val < 10 then 6 else 2))))

private def generatorRows (j : Fin 11) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0,0,0,1,3] else #[0,0]) else (if j.val < 3 then #[0,0,0,1,3] else (if j.val < 4 then #[0,0,1,1] else #[0,0,0,1,1,3]))) else (if j.val < 8 then (if j.val < 6 then #[0,0,0,1] else (if j.val < 7 then #[0,0,0,0,3] else #[0,0,0,3])) else (if j.val < 9 then #[0,0,0,1,1] else (if j.val < 10 then #[0,0,0,0,1,3] else #[0,0]))))

private def stateBasisRows (j : Fin 11) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,1,5,7,5,0] else #[0,1]) else (if j.val < 3 then #[1,5,7,5,0] else (if j.val < 4 then #[0,5,4,5] else #[0,4,7,4,5,0]))) else (if j.val < 8 then (if j.val < 6 then #[4,5,6,4] else (if j.val < 7 then #[0,1,4,5,0] else #[0,1,7,0])) else (if j.val < 9 then #[1,4,5,4,5] else (if j.val < 10 then #[1,5,7,11,5,0] else #[10,11]))))

private def termGenerator (j : Fin 11)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 11)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 11)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 131).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 131).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 131) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D131

namespace D132

private def displacementBasis (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 54 else 85) else (if j.val < 3 then 156 else (if j.val < 4 then 284 else 528))) else (if j.val < 8 then (if j.val < 6 then 1046 else (if j.val < 7 then 2069 else 4098)) else (if j.val < 9 then 8196 else (if j.val < 10 then 16392 else 32769))))

private def displacementDual (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 32 else 64) else (if j.val < 3 then 128 else (if j.val < 4 then 256 else 512))) else (if j.val < 8 then (if j.val < 6 then 1024 else (if j.val < 7 then 2048 else 4096)) else (if j.val < 9 then 8192 else (if j.val < 10 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 11 :=
  binaryCoordinateSpaceOfMasks 16 11
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 132).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 132).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 11) : ℕ :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 4 else 2) else (if j.val < 3 then 5 else (if j.val < 4 then 4 else 6))) else (if j.val < 8 then (if j.val < 6 then 4 else (if j.val < 7 then 3 else 4)) else (if j.val < 9 then 4 else (if j.val < 10 then 6 else 7))))

private def generatorRows (j : Fin 11) :
    Array (Fin 4) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[0,0,1,3] else #[0,0]) else (if j.val < 3 then #[0,0,0,1,3] else (if j.val < 4 then #[0,0,1,1] else #[0,0,0,1,1,3]))) else (if j.val < 8 then (if j.val < 6 then #[0,0,0,1] else (if j.val < 7 then #[0,0,3] else #[0,0,0,3])) else (if j.val < 9 then #[0,0,1,3] else (if j.val < 10 then #[0,0,0,0,1,3] else #[0,0,0,0,0,1,3]))))

private def stateBasisRows (j : Fin 11) :
    Array (Fin 12) :=
  (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then #[5,7,5,0] else #[0,1]) else (if j.val < 3 then #[0,5,7,5,0] else (if j.val < 4 then #[0,5,4,5] else #[1,4,7,4,5,0]))) else (if j.val < 8 then (if j.val < 6 then #[4,5,6,4] else (if j.val < 7 then #[4,5,0] else #[0,1,7,0])) else (if j.val < 9 then #[4,7,4,0] else (if j.val < 10 then #[1,5,7,11,5,0] else #[1,5,7,10,11,5,0]))))

private def termGenerator (j : Fin 11)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 11)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 11)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 132).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 132).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 132) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D132

namespace D133

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 30 else (if j.val < 2 then 39 else 75)) else (if j.val < 4 then 141 else (if j.val < 5 then 257 else 515))) else (if j.val < 9 then (if j.val < 7 then 1028 else (if j.val < 8 then 2060 else 4107)) else (if j.val < 10 then 8198 else (if j.val < 11 then 16398 else 32777))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 16 else (if j.val < 2 then 32 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 133).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 133).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 3 else (if j.val < 2 then 2 else 1)) else (if j.val < 4 then 2 else (if j.val < 5 then 3 else 3))) else (if j.val < 9 then (if j.val < 7 then 4 else (if j.val < 8 then 3 else 3)) else (if j.val < 10 then 5 else (if j.val < 11 then 2 else 4))))

private def generatorRows (j : Fin 12) :
    Array (Fin 4) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0,0] else (if j.val < 2 then #[0,0] else #[0])) else (if j.val < 4 then #[0,0] else (if j.val < 5 then #[0,1,1] else #[0,0,1]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,0,1] else (if j.val < 8 then #[0,0,1] else #[0,0,1])) else (if j.val < 10 then #[0,0,0,1,1] else (if j.val < 11 then #[0,0] else #[0,0,0,0]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 12) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,1,2] else (if j.val < 2 then #[0,3] else #[3])) else (if j.val < 4 then #[2,3] else (if j.val < 5 then #[5,4,5] else #[4,5,4]))) else (if j.val < 9 then (if j.val < 7 then #[4,5,6,4] else (if j.val < 8 then #[4,7,5] else #[3,5,5])) else (if j.val < 10 then #[2,4,5,4,5] else (if j.val < 11 then #[2,11] else #[2,3,10,11]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 133).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 133).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 133) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D133

namespace D134

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 30 else (if j.val < 2 then 39 else 75)) else (if j.val < 4 then 141 else (if j.val < 5 then 258 else 513))) else (if j.val < 9 then (if j.val < 7 then 1032 else (if j.val < 8 then 2052 else 4109)) else (if j.val < 10 then 8203 else (if j.val < 11 then 16391 else 32782))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 16 else (if j.val < 2 then 32 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 134).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 134).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 3 else (if j.val < 2 then 2 else 1)) else (if j.val < 4 then 2 else (if j.val < 5 then 3 else 3))) else (if j.val < 9 then (if j.val < 7 then 4 else (if j.val < 8 then 3 else 4)) else (if j.val < 10 then 5 else (if j.val < 11 then 2 else 3))))

private def generatorRows (j : Fin 12) :
    Array (Fin 4) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0,0] else (if j.val < 2 then #[0,0] else #[0])) else (if j.val < 4 then #[0,0] else (if j.val < 5 then #[0,1,1] else #[0,0,1]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,0,1] else (if j.val < 8 then #[0,0,1] else #[0,0,0,1])) else (if j.val < 10 then #[0,0,0,1,1] else (if j.val < 11 then #[0,0] else #[0,0,0]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 12) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,1,2] else (if j.val < 2 then #[0,3] else #[3])) else (if j.val < 4 then #[2,3] else (if j.val < 5 then #[5,4,5] else #[4,5,4]))) else (if j.val < 9 then (if j.val < 7 then #[4,5,6,4] else (if j.val < 8 then #[4,7,5] else #[2,3,5,5])) else (if j.val < 10 then #[3,4,5,4,5] else (if j.val < 11 then #[3,11] else #[2,10,11]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 134).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 134).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 134) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D134

namespace D135

private def displacementBasis (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 30 else (if j.val < 2 then 39 else 75)) else (if j.val < 4 then 141 else (if j.val < 5 then 259 else 514))) else (if j.val < 9 then (if j.val < 7 then 1036 else (if j.val < 8 then 2056 else 4102)) else (if j.val < 10 then 8205 else (if j.val < 11 then 16393 else 32775))))

private def displacementDual (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 16 else (if j.val < 2 then 32 else 64)) else (if j.val < 4 then 128 else (if j.val < 5 then 256 else 512))) else (if j.val < 9 then (if j.val < 7 then 1024 else (if j.val < 8 then 2048 else 4096)) else (if j.val < 10 then 8192 else (if j.val < 11 then 16384 else 32768))))

def displacementChart :
    BinaryCoordinateSpace 16 12 :=
  binaryCoordinateSpaceOfMasks 16 12
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 135).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 135).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 12) : ℕ :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 3 else (if j.val < 2 then 2 else 1)) else (if j.val < 4 then 2 else (if j.val < 5 then 3 else 3))) else (if j.val < 9 then (if j.val < 7 then 4 else (if j.val < 8 then 3 else 3)) else (if j.val < 10 then 6 else (if j.val < 11 then 3 else 3))))

private def generatorRows (j : Fin 12) :
    Array (Fin 4) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,0,0] else (if j.val < 2 then #[0,0] else #[0])) else (if j.val < 4 then #[0,0] else (if j.val < 5 then #[0,1,1] else #[0,0,1]))) else (if j.val < 9 then (if j.val < 7 then #[0,0,0,1] else (if j.val < 8 then #[0,0,1] else #[0,0,1])) else (if j.val < 10 then #[0,0,0,0,1,1] else (if j.val < 11 then #[0,0,0] else #[0,0,0]))))

private def stateBasisRows (j : Fin 12) :
    Array (Fin 12) :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then #[0,1,2] else (if j.val < 2 then #[0,3] else #[3])) else (if j.val < 4 then #[2,3] else (if j.val < 5 then #[5,4,5] else #[4,5,4]))) else (if j.val < 9 then (if j.val < 7 then #[4,5,6,4] else (if j.val < 8 then #[4,7,5] else #[2,5,5])) else (if j.val < 10 then #[2,3,4,5,4,5] else (if j.val < 11 then #[2,3,11] else #[3,10,11]))))

private def termGenerator (j : Fin 12)
    (t : Fin (termCount j)) : Fin 4 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 12)
    (t : Fin (termCount j)) : Fin 12 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 12)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 135).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 135).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 135) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D135

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

end
