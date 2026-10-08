import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleOrbits

/-! Executable orbit-word table for states 24–24. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryOrbitTableData24

abbrev Source := PrimitiveAffineEightFrameRow9ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow9TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩

private def wordDictionary : Array Source :=
  #[PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [0],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [6],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [0,6],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [2],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [3],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [4],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [5],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [2,6],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [3,6],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [1],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [1,3],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [1,0],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [1,5],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [0,2],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [0,1],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [0,4],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [1,2],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [0,3],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [1,0,6],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [1,6],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [1,3,6],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [1,1],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [0,1,6],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [0,2,6],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [0,5],PrimitiveAffineEightFrameRow9ModuleOrbits.sourceWord [0,3,6]]

private def childOrbitTable : Array (Array (Array (List ℕ))) :=
  #[#[#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]]

def childOrbitRows (i : Fin 1) (c : Fin 22) : Array (List Source) :=
  ((childOrbitTable[i.val]!)[c.val]!).map
    (fun row ↦ row.map (fun k ↦ wordDictionary[k]!))

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryOrbitTableData24
