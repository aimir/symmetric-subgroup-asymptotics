import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleRepresentation

/-! Executable selected invariant-state child table. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleRegistryChildTableData

private def childTable : Array (Array (Fin 16)) :=
  #[#[0,1,2,3,4,5,7,8,9,10,11,12,14,15],#[1,1,2,3,4,5,7,8,9,10,11,12,14,15],#[2,2,2,3,4,5,9,8,9,10,11,12,14,15],#[3,3,3,3,6,6,10,8,10,10,13,13,14,15],#[4,4,4,6,4,6,11,8,11,13,11,13,14,15],#[5,5,5,6,6,5,12,8,12,13,13,12,14,15],#[6,6,6,6,6,6,13,8,13,13,13,13,14,15],#[7,7,9,10,11,12,7,14,9,10,11,12,14,15],#[8,8,8,8,8,8,14,8,14,14,14,14,14,15],#[9,9,9,10,11,12,9,14,9,10,11,12,14,15],#[10,10,10,10,13,13,10,14,10,10,13,13,14,15],#[11,11,11,13,11,13,11,14,11,13,11,13,14,15],#[12,12,12,13,13,12,12,14,12,13,13,12,14,15],#[13,13,13,13,13,13,13,14,13,13,13,13,14,15],#[14,14,14,14,14,14,14,14,14,14,14,14,14,15],#[15,15,15,15,15,15,15,15,15,15,15,15,15,15]]

def child
    (i : Fin 16) (c : Fin 14) : Fin 16 :=
  (childTable[i.val]!)[c.val]!

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleRegistryChildTableData
