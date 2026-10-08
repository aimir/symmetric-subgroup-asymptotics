import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRepresentation

/-! Executable selected invariant-state child table. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistryChildTableData

private def childTable : Array (Array (Fin 11)) :=
  #[#[0,1,2,3,4,5,6,7,8,9,10],#[1,1,2,3,4,5,6,7,8,9,10],#[2,2,2,6,4,8,6,7,8,9,10],#[3,3,6,3,7,5,6,7,8,9,10],#[4,4,4,7,4,9,7,7,9,9,10],#[5,5,8,5,9,5,8,9,8,9,10],#[6,6,6,6,7,8,6,7,8,9,10],#[7,7,7,7,7,9,7,7,9,9,10],#[8,8,8,8,9,8,8,9,8,9,10],#[9,9,9,9,9,9,9,9,9,9,10],#[10,10,10,10,10,10,10,10,10,10,10]]

def child
    (i : Fin 11) (c : Fin 11) : Fin 11 :=
  (childTable[i.val]!)[c.val]!

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistryChildTableData
