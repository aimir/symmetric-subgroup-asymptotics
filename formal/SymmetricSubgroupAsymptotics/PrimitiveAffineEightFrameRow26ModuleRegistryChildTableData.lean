import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRepresentation

/-! Executable selected invariant-state child table. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistryChildTableData

private def childTable : Array (Array (Fin 15)) :=
  #[#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],#[1,1,2,3,4,5,6,7,8,9,10,11,12,13,14],#[2,2,2,3,5,5,6,7,8,9,10,11,12,13,14],#[3,3,3,3,6,6,6,7,8,9,10,11,12,13,14],#[4,4,5,6,4,5,6,7,8,9,10,11,12,13,14],#[5,5,5,6,5,5,6,7,8,9,10,11,12,13,14],#[6,6,6,6,6,6,6,7,8,9,10,11,12,13,14],#[7,7,7,7,7,7,7,7,8,9,10,11,12,13,14],#[8,8,8,8,8,8,8,8,8,9,10,11,12,13,14],#[9,9,9,9,9,9,9,9,9,9,10,12,12,13,14],#[10,10,10,10,10,10,10,10,10,10,10,13,13,13,14],#[11,11,11,11,11,11,11,11,11,12,13,11,12,13,14],#[12,12,12,12,12,12,12,12,12,12,13,12,12,13,14],#[13,13,13,13,13,13,13,13,13,13,13,13,13,13,14],#[14,14,14,14,14,14,14,14,14,14,14,14,14,14,14]]

def child
    (i : Fin 15) (c : Fin 15) : Fin 15 :=
  (childTable[i.val]!)[c.val]!

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistryChildTableData
