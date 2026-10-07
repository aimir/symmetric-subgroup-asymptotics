import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 48–48. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleRegistry

local instance sourceGroupDisplacement48 : Group Source := PrimitiveAffineEightFrameRow20TopCertificate.group
local instance sourceInhabitedDisplacement48 : Inhabited Source := ⟨1⟩

namespace D48

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
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 48).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 48).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 16) : ℕ :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 5 else 5) else (if j.val < 3 then 6 else 6)) else (if j.val < 6 then (if j.val < 5 then 5 else 5) else (if j.val < 7 then 6 else 4))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 1 else 2) else (if j.val < 11 then 2 else 3)) else (if j.val < 14 then (if j.val < 13 then 6 else 4) else (if j.val < 15 then 7 else 5))))

private def generatorRows (j : Fin 16) :
    Array (Fin 3) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[0,1,1,1,2] else #[0,1,1,2,2]) else (if j.val < 3 then #[0,0,1,1,1,2] else #[0,0,1,1,2,2])) else (if j.val < 6 then (if j.val < 5 then #[0,1,1,1,2] else #[0,0,1,1,2]) else (if j.val < 7 then #[0,0,1,1,1,2] else #[0,1,1,2]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[1] else #[1,1]) else (if j.val < 11 then #[0,1] else #[0,1,1])) else (if j.val < 14 then (if j.val < 13 then #[0,1,1,1,2,2] else #[0,1,1,2]) else (if j.val < 15 then #[0,0,1,1,1,2,2] else #[0,0,1,1,2]))))

private def stateBasisRows (j : Fin 16) :
    Array (Fin 16) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[4,0,1,4,1] else #[5,0,5,0,1]) else (if j.val < 3 then #[0,4,0,1,4,1] else #[1,5,0,5,0,1])) else (if j.val < 6 then (if j.val < 5 then #[5,0,4,5,0] else #[4,5,1,4,1]) else (if j.val < 7 then #[4,5,0,4,5,0] else #[4,1,4,1]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[9] else #[8,9]) else (if j.val < 11 then #[8,9] else #[9,8,9])) else (if j.val < 14 then (if j.val < 13 then #[4,0,1,4,0,1] else #[5,0,5,0]) else (if j.val < 15 then #[4,12,0,1,4,0,1] else #[5,13,0,5,0]))))

private def termGenerator (j : Fin 16)
    (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 16)
    (t : Fin (termCount j)) : Fin 16 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 16)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 48).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow20ModuleRepresentation.charts 48).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow20ModuleRepresentation.representation PrimitiveAffineEightFrameRow20TopCertificate.ambient
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states 48) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D48

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleRegistry

end
