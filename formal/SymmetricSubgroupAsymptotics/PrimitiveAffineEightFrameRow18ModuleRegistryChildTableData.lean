import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleRepresentation

/-! Executable selected invariant-state child table. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleRegistryChildTableData

private def childTable : Array (Array (Fin 5)) :=
  #[#[0,1,2,3,4],#[1,1,2,3,4],#[2,2,2,3,4],#[3,3,3,3,4],#[4,4,4,4,4]]

def child
    (i : Fin 5) (c : Fin 5) : Fin 5 :=
  (childTable[i.val]!)[c.val]!

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleRegistryChildTableData
