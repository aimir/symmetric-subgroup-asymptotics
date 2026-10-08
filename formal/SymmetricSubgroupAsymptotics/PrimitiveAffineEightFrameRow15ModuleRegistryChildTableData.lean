import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRepresentation

/-! Executable selected invariant-state child table. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistryChildTableData

private def childTable : Array (Array (Fin 6)) :=
  #[#[0,1,2,3,4,5],#[1,1,2,3,4,5],#[2,2,2,4,4,5],#[3,3,4,3,4,5],#[4,4,4,4,4,5],#[5,5,5,5,5,5]]

def child
    (i : Fin 6) (c : Fin 6) : Fin 6 :=
  (childTable[i.val]!)[c.val]!

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistryChildTableData
