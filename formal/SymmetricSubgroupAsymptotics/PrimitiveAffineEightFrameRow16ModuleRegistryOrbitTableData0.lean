import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleOrbits

/-! Executable orbit-word table for states 0–6. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistryOrbitTableData0

abbrev Source := PrimitiveAffineEightFrameRow16ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩

private def wordDictionary : Array Source :=
  #[PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [0],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [7],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [0,7],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [3],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [2],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [3,7],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [2,7],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [4],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [2,4],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [5],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [0,5],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [1],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [0,1],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [0,2],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [1,7],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [0,1,7],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [0,2,7],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [1,0],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [1,3],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [4,7],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [1,0,7],PrimitiveAffineEightFrameRow16ModuleOrbits.sourceWord [1,3,7]]

private def childOrbitTable : Array (Array (Array (List ℕ))) :=
  #[#[#[],#[[0],[1],[2],[3]],#[[0],[1],[4],[0,1,5],[2],[3],[6],[2,3,7]],#[[0],[1],[4],[1,5,4],[2],[3],[6],[3,7,6]],#[[8,9],[0,5,8,9],[0],[1],[8],[0,1,8,2],[8,10],[0,1,8,2,11]],#[[0],[1],[12],[13],[12,5],[13,14],[2],[3],[15],[16],[15,7],[16,17]],#[[0],[8],[4],[1],[12],[18],[19],[14],[2],[20],[6],[3],[15],[21],[22],[17]]],#[#[[],[],[],[]],#[[],[],[],[]],#[[0],[1],[0],[1],[2],[3],[2],[3]],#[[0],[1],[0],[1],[2],[3],[2],[3]],#[[],[],[0],[1],[8],[0,1,8,2],[0,8],[0,8,2]],#[[0],[1],[12],[13],[0,12],[1,13],[2],[3],[15],[16],[2,15],[3,16]],#[[0],[8],[4],[1],[12],[1,8,14],[0,12,4],[14],[2],[20],[6],[3],[15],[3,20,17],[2,15,6],[17]]],#[#[[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[]],#[[0],[1],[1],[0,1],[0,1],[0],[2],[3],[3],[2,3],[2,3],[2]],#[[8,2],[1,8],[1,8],[1,2],[1,2],[8,2],[0,1,8],[1,8,2],[1,8,2],[0,2],[0,2],[0,1,8]],#[[0],[1],[1],[0,1],[0,1],[0],[2],[3],[3],[2,3],[2,3],[2]],#[[0],[0,1,12],[4],[1],[12],[0,1,4],[0,12,4],[1,12,4],[2],[2,3,15],[6],[3],[15],[2,3,6],[2,15,6],[3,15,6]]],#[#[[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[]],#[[0],[1],[0,1],[0],[1],[0,1],[2],[3],[2,3],[2],[3],[2,3]],#[[],[],[],[],[],[],[],[]],#[[0,1,8],[1,8,2],[0,2],[0,1,8],[1,8,2],[0,2],[1,8],[8,2],[1,2],[1,8],[8,2],[1,2]],#[[0],[1],[0,1],[0],[1],[0,1],[2],[3],[2,3],[2],[3],[2,3]],#[[0],[1,12,4],[4],[1],[12],[0,1,12],[0,12,4],[0,1,4],[2],[3,15,6],[6],[3],[15],[2,3,15],[2,15,6],[2,3,6]]],#[#[[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[]],#[[0,3],[1,2],[0,1,2],[0,2,3],[1,2,3],[0,1,3],[0,2],[1,3],[1,2,3],[0,1,2],[0,1,3],[0,2,3]],#[[0,2],[1,3],[1,2,3],[0,1,2],[0,1,3],[0,2,3],[1,2],[0,3],[0,1,3],[1,2,3],[0,2,3],[0,1,2]],#[[],[],[],[],[],[],[],[]],#[[0],[1],[12],[0,1,12,2],[0,12],[0,12,2],[2],[0,1,2],[0,12],[12],[0,12,2],[0,1,12,2]],#[[0],[8],[4],[1],[12],[1,8,14],[0,12,4],[14],[2],[0,1,12,14,3],[12,4,8,2,14],[3],[12,4,2],[1,14,3],[8,2,14],[0,12,3]]],#[#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[0],[1],[0],[1],[0],[1],[0],[1],[2],[3],[2],[3],[2],[3],[2],[3]]],#[#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]]

def childOrbitRows (i : Fin 7) (c : Fin 7) : Array (List Source) :=
  ((childOrbitTable[i.val]!)[c.val]!).map
    (fun row ↦ row.map (fun k ↦ wordDictionary[k]!))

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistryOrbitTableData0
