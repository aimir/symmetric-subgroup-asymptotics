import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistryJoinData

/-! Selected invariant-state displacement certificates 16–16. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistry

local instance sourceGroupDisplacement16 : Group Source := PrimitiveAffineEightFrameTop15TopCertificate.group
local instance sourceInhabitedDisplacement16 : Inhabited Source := ⟨1⟩

namespace D16

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
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 16).toSubmodule := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply ((PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 16).2.mem_iff _).mpr
  fin_cases j <;> native_decide

private def termCount (j : Fin 16) : ℕ :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 6 else 6) else (if j.val < 3 then 7 else 7)) else (if j.val < 6 then (if j.val < 5 then 6 else 5) else (if j.val < 7 then 7 else 6))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 7 else 4) else (if j.val < 11 then 8 else 5)) else (if j.val < 14 then (if j.val < 13 then 7 else 5) else (if j.val < 15 then 8 else 6))))

private def generatorRows (j : Fin 16) :
    Array (Fin 5) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[3,3,3,3,4,4] else #[3,3,3,3,3,4]) else (if j.val < 3 then #[0,3,3,3,3,4,4] else #[0,3,3,3,3,3,4])) else (if j.val < 6 then (if j.val < 5 then #[3,3,3,3,4,4] else #[3,3,3,3,4]) else (if j.val < 7 then #[2,3,3,3,3,4,4] else #[2,3,3,3,3,4]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[3,3,3,3,3,4,4] else #[3,3,3,4]) else (if j.val < 11 then #[1,3,3,3,3,3,4,4] else #[1,3,3,3,4])) else (if j.val < 14 then (if j.val < 13 then #[3,3,3,3,3,4,4] else #[3,3,3,3,4]) else (if j.val < 15 then #[0,3,3,3,3,3,4,4] else #[0,3,3,3,3,4]))))

private def stateBasisRows (j : Fin 16) :
    Array (Fin 16) :=
  (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then #[1,5,8,9,0,1] else #[0,1,4,5,9,0]) else (if j.val < 3 then #[0,1,5,8,9,0,1] else #[1,0,1,4,5,9,0])) else (if j.val < 6 then (if j.val < 5 then #[0,1,5,9,0,1] else #[0,4,5,8,0]) else (if j.val < 7 then #[4,0,1,5,9,0,1] else #[5,0,4,5,8,0]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then #[0,1,5,8,9,0,1] else #[1,4,8,1]) else (if j.val < 11 then #[8,0,1,5,8,9,0,1] else #[9,1,4,8,1])) else (if j.val < 14 then (if j.val < 13 then #[0,1,4,5,9,0,1] else #[1,5,8,9,1]) else (if j.val < 15 then #[12,0,1,4,5,9,0,1] else #[13,1,5,8,9,1]))))

private def termGenerator (j : Fin 16)
    (t : Fin (termCount j)) : Fin 5 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin 16)
    (t : Fin (termCount j)) : Fin 16 :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin 16)
    (t : Fin (termCount j)) :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 16).toSubmodule :=
  ⟨(PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 16).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow24ModuleRepresentation.representation PrimitiveAffineEightFrameTop15TopCertificate.ambient
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 16) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D16

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistry

end
