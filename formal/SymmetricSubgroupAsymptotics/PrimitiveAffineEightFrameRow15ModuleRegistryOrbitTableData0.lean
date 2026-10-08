import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleOrbits

/-! Executable orbit-word table for states 0–5. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistryOrbitTableData0

abbrev Source := PrimitiveAffineEightFrameRow15ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩

private def wordDictionary : Array Source :=
  #[PrimitiveAffineEightFrameRow15ModuleOrbits.sourceWord [],PrimitiveAffineEightFrameRow15ModuleOrbits.sourceWord [0],PrimitiveAffineEightFrameRow15ModuleOrbits.sourceWord [7],PrimitiveAffineEightFrameRow15ModuleOrbits.sourceWord [0,7],PrimitiveAffineEightFrameRow15ModuleOrbits.sourceWord [3],PrimitiveAffineEightFrameRow15ModuleOrbits.sourceWord [2],PrimitiveAffineEightFrameRow15ModuleOrbits.sourceWord [3,7],PrimitiveAffineEightFrameRow15ModuleOrbits.sourceWord [2,7],PrimitiveAffineEightFrameRow15ModuleOrbits.sourceWord [1],PrimitiveAffineEightFrameRow15ModuleOrbits.sourceWord [0,1],PrimitiveAffineEightFrameRow15ModuleOrbits.sourceWord [0,2],PrimitiveAffineEightFrameRow15ModuleOrbits.sourceWord [1,7],PrimitiveAffineEightFrameRow15ModuleOrbits.sourceWord [0,1,7],PrimitiveAffineEightFrameRow15ModuleOrbits.sourceWord [0,2,7],PrimitiveAffineEightFrameRow15ModuleOrbits.sourceWord [4],PrimitiveAffineEightFrameRow15ModuleOrbits.sourceWord [2,3],PrimitiveAffineEightFrameRow15ModuleOrbits.sourceWord [4,7],PrimitiveAffineEightFrameRow15ModuleOrbits.sourceWord [2,3,7]]

private def childOrbitTable : Array (Array (Array (List ℕ))) :=
  #[#[#[],#[[0],[1],[2],[3]],#[[0],[1],[4],[0,1,5],[2],[3],[6],[2,3,7]],#[[0],[1],[4],[1,5,4],[2],[3],[6],[3,7,6]],#[[0],[1],[8,9],[8],[8,5,9],[8,10],[2],[3],[11,12],[11],[11,7,12],[11,13]],#[[0],[14],[4],[1],[5],[8],[15],[10],[2],[16],[6],[3],[7],[11],[17],[13]]],#[#[[],[],[],[]],#[[],[],[],[]],#[[0],[1],[0],[1],[2],[3],[2],[3]],#[[0],[1],[0],[1],[2],[3],[2],[3]],#[[0],[1],[8,9],[8],[0,8,9],[1,8],[2],[3],[11,12],[11],[2,11,12],[3,11]],#[[0],[14],[4],[1],[5],[8],[0,5,4],[1,8,14],[2],[16],[6],[3],[7],[11],[2,7,6],[3,11,16]]],#[#[[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[]],#[[0],[1],[1],[0,1],[0,1],[0],[2],[3],[3],[2,3],[2,3],[2]],#[[0],[1],[1],[0,1],[0,1],[0],[2],[3],[3],[2,3],[2,3],[2]],#[[0],[0,1,5],[0,1,8],[1],[5],[8],[1,8,5],[0,8,5],[2],[2,3,7],[2,3,11],[3],[7],[11],[3,11,7],[2,11,7]]],#[#[[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[]],#[[0],[1],[0,1],[0],[1],[0,1],[2],[3],[2,3],[2],[3],[2,3]],#[[],[],[],[],[],[],[],[]],#[[0],[1],[0,1],[0],[1],[0,1],[2],[3],[2,3],[2],[3],[2,3]],#[[0],[0,8,4],[4],[1],[0,1,8],[8],[1,8,4],[0,1,4],[2],[2,11,6],[6],[3],[2,3,11],[11],[3,11,6],[2,3,6]]],#[#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[]],#[[0],[1],[0],[1],[0],[1],[0],[1],[2],[3],[2],[3],[2],[3],[2],[3]]],#[#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]]

def childOrbitRows (i : Fin 6) (c : Fin 6) : Array (List Source) :=
  ((childOrbitTable[i.val]!)[c.val]!).map
    (fun row ↦ row.map (fun k ↦ wordDictionary[k]!))

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistryOrbitTableData0
