import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleRepresentation

/-! Executable selected invariant-state child table. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleRegistryChildTableData

private def childTable : Array (Array (Fin 14)) :=
  #[#[0,1,2,3,4,5,6,7,8,9,10,11,12,13],#[1,1,2,3,4,5,6,7,8,9,10,11,12,13],#[2,2,2,3,4,5,6,7,8,9,10,11,12,13],#[3,3,3,3,7,7,8,7,8,11,11,11,12,13],#[4,4,4,7,4,7,9,7,11,9,11,11,12,13],#[5,5,5,7,7,5,10,7,11,11,10,11,12,13],#[6,6,6,8,9,10,6,11,8,9,10,11,12,13],#[7,7,7,7,7,7,11,7,11,11,11,11,12,13],#[8,8,8,8,11,11,8,11,8,11,11,11,12,13],#[9,9,9,11,9,11,9,11,11,9,11,11,12,13],#[10,10,10,11,11,10,10,11,11,11,10,11,12,13],#[11,11,11,11,11,11,11,11,11,11,11,11,12,13],#[12,12,12,12,12,12,12,12,12,12,12,12,12,13],#[13,13,13,13,13,13,13,13,13,13,13,13,13,13]]

def child
    (i : Fin 14) (c : Fin 14) : Fin 14 :=
  (childTable[i.val]!)[c.val]!

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleRegistryChildTableData
