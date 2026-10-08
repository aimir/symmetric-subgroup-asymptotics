import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleRepresentation

/-! Executable old-coordinate table for states 0–4. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleRegistryOldTableData0

private def childOldTable : Array (Array (Array ℕ)) :=
  #[#[#[],#[0,0,0,0],#[0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],#[#[1,2,4,8],#[1,2,4,8],#[1,2,0,0,0,0,4,8],#[0,0,0,0,1,2,0,0,0,0,4,8],#[0,0,0,0,0,0,1,2,0,0,0,0,0,0,4,8]],#[#[1,2,4,8,16,32,64,128],#[1,2,4,8,16,32,64,128],#[1,2,4,8,16,32,64,128],#[0,0,0,4,1,6,0,12,16,32,68,132],#[0,0,0,0,0,0,1,2,0,0,4,8,16,32,64,128]],#[#[1,2,4,8,16,32,64,128,256,512,1024,2048],#[1,2,4,8,16,32,64,128,256,512,1024,2048],#[1,2,4,8,16,32,64,128,256,512,1024,2048],#[1,2,4,8,16,32,64,128,256,512,1024,2048],#[0,0,1,2,4,8,16,32,0,0,64,128,256,512,1024,2048]],#[#[1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768],#[1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768],#[1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768],#[1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768],#[1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]]]

def childOldMasks (i : Fin 5) (c : Fin 5) : Array ℕ :=
  (childOldTable[i.val]!)[c.val]!

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleRegistryOldTableData0
