import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleOrbits

/-! Executable orbit-word table for states 8–11. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistryOrbitTableData8

abbrev Source := PrimitiveAffineEightFrameRow17ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩

private def wordDictionary : Array Source :=
  #[PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [0],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [7],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [0,7],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [2],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [3],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [5],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [6],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [2,7],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [3,7],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [1,0],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [1],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [1,3],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [4,0],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [4],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [4,6],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [1,0,7],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [1,7],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [1,3,7],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [0,1],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [0,2],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [0,4],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [0,5],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [0,1,7],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [0,2,7],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [0,3],PrimitiveAffineEightFrameRow17ModuleOrbits.sourceWord [0,3,7]]

private def childOrbitTable : Array (Array (Array (List ℕ))) :=
  #[#[#[[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[0],[0],[0],[],[],[0]],#[[],[],[],[],[],[],[],[],[],[]],#[[0],[0],[0],[],[],[0],[2],[2],[2],[],[],[2]],#[[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[0],[0],[0],[],[],[0]],#[[0],[0],[0],[],[],[0],[2],[2],[2],[],[],[2]],#[[0],[0,1,4],[4],[1],[4],[0,1,4],[0],[1],[2],[2,3,8],[8],[3],[8],[2,3,8],[2],[3]]],#[#[[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[]],#[[0],[0],[0],[],[],[0],[0],[0],[0],[],[],[0]],#[[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[]],#[[0],[0],[0],[],[],[0],[0],[0],[0],[],[],[0]],#[[0],[0,1,4],[4],[1],[4],[0,1,4],[0],[1],[2],[0,4,3],[0,4,2],[3],[0,4,2],[0,4,3],[2],[3]]],#[#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[0],[1],[0],[1],[0],[1],[0],[1],[2],[3],[2],[3],[2],[3],[2],[3]]],#[#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]]

def childOrbitRows (i : Fin 4) (c : Fin 12) : Array (List Source) :=
  ((childOrbitTable[i.val]!)[c.val]!).map
    (fun row ↦ row.map (fun k ↦ wordDictionary[k]!))

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistryOrbitTableData8
