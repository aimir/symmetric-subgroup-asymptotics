import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRepresentation

/-! Executable selected invariant-state child table. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistryChildTableData

private def childTable : Array (Array (Fin 17)) :=
  #[#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],#[1,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],#[2,2,2,3,5,5,6,7,8,9,10,11,12,13,14,15,16],#[3,3,3,3,6,6,6,7,8,9,10,11,12,13,14,15,16],#[4,4,5,6,4,5,6,7,8,9,10,11,12,13,14,15,16],#[5,5,5,6,5,5,6,7,8,9,10,11,12,13,14,15,16],#[6,6,6,6,6,6,6,7,8,9,10,11,12,13,14,15,16],#[7,7,7,7,7,7,7,7,10,10,10,11,12,13,14,15,16],#[8,8,8,8,8,8,8,10,8,10,10,11,12,13,14,15,16],#[9,9,9,9,9,9,9,10,10,9,10,11,12,13,14,15,16],#[10,10,10,10,10,10,10,10,10,10,10,11,12,13,14,15,16],#[11,11,11,11,11,11,11,11,11,11,11,11,12,14,14,15,16],#[12,12,12,12,12,12,12,12,12,12,12,12,12,15,15,15,16],#[13,13,13,13,13,13,13,13,13,13,13,14,15,13,14,15,16],#[14,14,14,14,14,14,14,14,14,14,14,14,15,14,14,15,16],#[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,16],#[16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16]]

def child
    (i : Fin 17) (c : Fin 17) : Fin 17 :=
  (childTable[i.val]!)[c.val]!

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistryChildTableData
