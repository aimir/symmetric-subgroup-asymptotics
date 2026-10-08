import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRepresentation

/-! Executable selected invariant-state child table. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistryChildTableData

private def childTable : Array (Array (Fin 12)) :=
  #[#[0,1,2,3,4,5,6,7,8,9,10,11],#[1,1,2,3,4,5,6,7,8,9,10,11],#[2,2,2,3,4,5,7,7,8,9,10,11],#[3,3,3,3,4,5,8,8,8,9,10,11],#[4,4,4,4,4,5,9,9,9,9,10,11],#[5,5,5,5,5,5,10,10,10,10,10,11],#[6,6,7,8,9,10,6,7,8,9,10,11],#[7,7,7,8,9,10,7,7,8,9,10,11],#[8,8,8,8,9,10,8,8,8,9,10,11],#[9,9,9,9,9,10,9,9,9,9,10,11],#[10,10,10,10,10,10,10,10,10,10,10,11],#[11,11,11,11,11,11,11,11,11,11,11,11]]

def child
    (i : Fin 12) (c : Fin 12) : Fin 12 :=
  (childTable[i.val]!)[c.val]!

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistryChildTableData
