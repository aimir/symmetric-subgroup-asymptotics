import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleOrbits

/-! Executable orbit-word table for states 8–11. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistryOrbitTableData8

abbrev Source := PrimitiveAffineEightFrameRow19ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop10TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩

private def wordDictionary : Array Source :=
  #[PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [0],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [8],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [0,8],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [1],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [2],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [4],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [5],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [1,8],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [2,8],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [7],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [6],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [7,8],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [0,0],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [0,2],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [3],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [3,3],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [3,5],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [0,0,8],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [0,2,8],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [0,7],PrimitiveAffineEightFrameRow19ModuleOrbits.sourceWord [0,7,8]]

private def childOrbitTable : Array (Array (Array (List ℕ))) :=
  #[#[#[[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[0],[0],[],[0],[0],[]],#[[0],[0],[],[0],[0],[],[2],[2],[],[2],[2],[]],#[[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[0],[0],[],[0],[0],[]],#[[0],[0],[],[0],[0],[],[2],[2],[],[2],[2],[]],#[[0],[0,1,5],[5],[1],[0],[1],[5],[0,1,5],[2],[2,3,9],[9],[3],[2],[3],[9],[2,3,9]]],#[#[[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[]],#[[0],[0],[],[0],[0],[],[0],[0],[],[0],[0],[]],#[[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[]],#[[0],[0],[],[0],[0],[],[0],[0],[],[0],[0],[]],#[[0],[0,1,5],[5],[1],[0],[1],[5],[0,1,5],[2],[0,5,3],[0,5,2],[3],[2],[3],[0,5,2],[0,5,3]]],#[#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[0],[1],[0],[1],[0],[1],[0],[1],[2],[3],[2],[3],[2],[3],[2],[3]]],#[#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]]

def childOrbitRows (i : Fin 4) (c : Fin 12) : Array (List Source) :=
  ((childOrbitTable[i.val]!)[c.val]!).map
    (fun row ↦ row.map (fun k ↦ wordDictionary[k]!))

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistryOrbitTableData8
