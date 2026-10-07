import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRepresentation

/-! Executable selected invariant-state child table. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryChildTableData

private def childTable : Array (Array (Fin 17)) :=
  #[#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],#[1,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],#[2,2,2,6,6,8,6,12,8,11,11,11,12,15,15,15,16],#[3,3,6,3,6,10,6,13,11,11,10,11,15,13,15,15,16],#[4,4,6,6,4,9,6,14,11,9,11,11,15,15,14,15,16],#[5,5,8,10,9,5,11,7,8,9,10,11,12,13,14,15,16],#[6,6,6,6,6,11,6,15,11,11,11,11,15,15,15,15,16],#[7,7,12,13,14,7,15,7,12,14,13,15,12,13,14,15,16],#[8,8,8,11,11,8,11,12,8,11,11,11,12,15,15,15,16],#[9,9,11,11,9,9,11,14,11,9,11,11,15,15,14,15,16],#[10,10,11,10,11,10,11,13,11,11,10,11,15,13,15,15,16],#[11,11,11,11,11,11,11,15,11,11,11,11,15,15,15,15,16],#[12,12,12,15,15,12,15,12,12,15,15,15,12,15,15,15,16],#[13,13,15,13,15,13,15,13,15,15,13,15,15,13,15,15,16],#[14,14,15,15,14,14,15,14,15,14,15,15,15,15,14,15,16],#[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,16],#[16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16]]

def child
    (i : Fin 17) (c : Fin 17) : Fin 17 :=
  (childTable[i.val]!)[c.val]!

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryChildTableData
