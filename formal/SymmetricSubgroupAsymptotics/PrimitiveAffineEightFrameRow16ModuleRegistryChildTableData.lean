import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRepresentation

/-! Executable selected invariant-state child table. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistryChildTableData

private def childTable : Array (Array (Fin 7)) :=
  #[#[0,1,2,3,4,5,6],#[1,1,2,3,4,5,6],#[2,2,2,5,5,5,6],#[3,3,5,3,5,5,6],#[4,4,5,5,4,5,6],#[5,5,5,5,5,5,6],#[6,6,6,6,6,6,6]]

def child
    (i : Fin 7) (c : Fin 7) : Fin 7 :=
  (childTable[i.val]!)[c.val]!

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistryChildTableData
