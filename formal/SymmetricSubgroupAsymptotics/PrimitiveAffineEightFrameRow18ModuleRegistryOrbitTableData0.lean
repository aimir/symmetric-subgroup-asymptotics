import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleOrbits

/-! Executable orbit-word table for states 0–4. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleRegistryOrbitTableData0

abbrev Source := PrimitiveAffineEightFrameRow18ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop10TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩

private def wordDictionary : Array Source :=
  #[PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [3],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [8],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [3,8],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [2,3],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [2],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [0],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [4],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [0,4],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [0,3],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [1],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [1,3],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [0,8],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [0,3,8],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [1,8],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [1,3,8],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [0,2],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [0,2,3],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [2,8],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [2,3,8],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [0,2,8],PrimitiveAffineEightFrameRow18ModuleOrbits.sourceWord [0,2,3,8]]

private def childOrbitTable : Array (Array (Array (List ℕ))) :=
  #[#[#[],#[[0],[1],[2],[3]],#[[1,4],[0,5,1,4],[0],[6],[1],[1,2],[1,7],[1,2,8]],#[[0],[1],[6],[9],[6,10],[9,11],[2],[3],[12],[13],[12,14],[13,15]],#[[0],[1],[5],[4],[6],[9],[16],[17],[2],[3],[18],[19],[12],[13],[20],[21]]],#[#[[],[],[],[]],#[[],[],[],[]],#[[],[],[0],[6],[1],[1,2],[0,1],[6,1,2]],#[[0],[1],[6],[9],[0,6],[1,9],[2],[3],[12],[13],[2,12],[3,13]],#[[0],[1],[5],[4],[6],[9],[0,6,5],[1,9,4],[2],[3],[18],[19],[12],[13],[2,12,18],[3,13,19]]],#[#[[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[]],#[[0],[1],[6],[6,2],[0,6],[6,1,2],[2],[0,1,2],[6],[0,6],[6,2],[6,1,2]],#[[0],[1],[5],[4],[6],[9],[0,6,5],[1,9,4],[2],[3],[0,6,1,2,9],[6,5,9,4,3],[0,6,2],[6,5,3],[1,2,9],[9,4,3]]],#[#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[0],[1],[0],[1],[0],[1],[0],[1],[2],[3],[2],[3],[2],[3],[2],[3]]],#[#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]]

def childOrbitRows (i : Fin 5) (c : Fin 5) : Array (List Source) :=
  ((childOrbitTable[i.val]!)[c.val]!).map
    (fun row ↦ row.map (fun k ↦ wordDictionary[k]!))

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleRegistryOrbitTableData0
