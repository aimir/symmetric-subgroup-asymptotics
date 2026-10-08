import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow11ModuleRepresentation

/-! Executable selected invariant-state child table. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow11ModuleRegistryChildTableData

private def childTable : Array (Array (Fin 10)) :=
  #[#[0,1,2,3,4,5,6,7,8,9],#[1,1,2,3,4,5,6,7,8,9],#[2,2,2,3,4,5,6,7,8,9],#[3,3,3,3,6,5,6,7,8,9],#[4,4,4,6,4,7,6,7,8,9],#[5,5,5,5,7,5,7,7,8,9],#[6,6,6,6,6,7,6,7,8,9],#[7,7,7,7,7,7,7,7,8,9],#[8,8,8,8,8,8,8,8,8,9],#[9,9,9,9,9,9,9,9,9,9]]

def child
    (i : Fin 10) (c : Fin 10) : Fin 10 :=
  (childTable[i.val]!)[c.val]!

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow11ModuleRegistryChildTableData
