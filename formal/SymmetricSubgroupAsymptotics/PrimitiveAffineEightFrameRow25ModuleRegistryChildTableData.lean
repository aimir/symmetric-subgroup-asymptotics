import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleRepresentation

/-! Executable selected invariant-state child table. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleRegistryChildTableData

private def childTable : Array (Array (Fin 17)) :=
  #[#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],#[1,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],#[2,2,2,5,4,5,6,7,8,9,10,11,12,13,14,15,16],#[3,3,5,3,6,5,6,7,8,9,10,11,12,13,14,15,16],#[4,4,4,6,4,6,6,7,8,9,10,11,12,13,14,15,16],#[5,5,5,5,6,5,6,7,8,9,10,11,12,13,14,15,16],#[6,6,6,6,6,6,6,7,8,9,10,11,12,13,14,15,16],#[7,7,7,7,7,7,7,7,10,10,10,11,12,13,14,15,16],#[8,8,8,8,8,8,8,10,8,10,10,11,12,13,14,15,16],#[9,9,9,9,9,9,9,10,10,9,10,11,12,13,14,15,16],#[10,10,10,10,10,10,10,10,10,10,10,11,12,13,14,15,16],#[11,11,11,11,11,11,11,11,11,11,11,11,14,13,14,15,16],#[12,12,12,12,12,12,12,12,12,12,12,14,12,15,14,15,16],#[13,13,13,13,13,13,13,13,13,13,13,13,15,13,15,15,16],#[14,14,14,14,14,14,14,14,14,14,14,14,14,15,14,15,16],#[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,16],#[16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16]]

def child
    (i : Fin 17) (c : Fin 17) : Fin 17 :=
  (childTable[i.val]!)[c.val]!

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleRegistryChildTableData
