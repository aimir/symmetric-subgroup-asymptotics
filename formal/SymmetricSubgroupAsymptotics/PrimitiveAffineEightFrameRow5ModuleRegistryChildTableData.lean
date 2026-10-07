import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRepresentation

/-! Executable selected invariant-state child table. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRegistryChildTableData

private def childTable : Array (Array (Fin 14)) :=
  #[#[0,1,2,3,4,5,6,7,8,9,10,11,12,13],#[1,1,4,4,4,5,6,7,8,9,10,11,12,13],#[2,4,2,4,4,5,6,7,8,9,10,11,12,13],#[3,4,4,3,4,5,6,7,8,9,10,11,12,13],#[4,4,4,4,4,5,6,7,8,9,10,11,12,13],#[5,5,5,5,5,5,6,8,8,9,10,11,12,13],#[6,6,6,6,6,6,6,9,9,9,10,11,12,13],#[7,7,7,7,7,8,9,7,8,9,10,11,12,13],#[8,8,8,8,8,8,9,8,8,9,10,11,12,13],#[9,9,9,9,9,9,9,9,9,9,10,11,12,13],#[10,10,10,10,10,10,10,10,10,10,10,13,13,13],#[11,11,11,11,11,11,11,11,11,11,13,11,13,13],#[12,12,12,12,12,12,12,12,12,12,13,13,12,13],#[13,13,13,13,13,13,13,13,13,13,13,13,13,13]]

def child
    (i : Fin 14) (c : Fin 14) : Fin 14 :=
  (childTable[i.val]!)[c.val]!

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRegistryChildTableData
