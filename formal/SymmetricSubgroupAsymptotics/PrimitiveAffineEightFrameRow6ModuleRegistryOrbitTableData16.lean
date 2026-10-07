import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleOrbits

/-! Executable orbit-word table for states 16–16. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryOrbitTableData16

abbrev Source := PrimitiveAffineEightFrameRow6ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow6TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩

private def wordDictionary : Array Source :=
  #[PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [3],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [6],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [3,6],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [2],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [1],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [0],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [5],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [4],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [0,6],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [2,6],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [1,6],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [1,3],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [0,3],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [0,4],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [2,3],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [0,3,6],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [1,3,6],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [0,2],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [0,2,3],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [2,3,6],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [0,2,6],PrimitiveAffineEightFrameRow6ModuleOrbits.sourceWord [0,2,3,6]]

private def childOrbitTable : Array (Array (Array (List ℕ))) :=
  #[#[#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]]

def childOrbitRows (i : Fin 1) (c : Fin 17) : Array (List Source) :=
  ((childOrbitTable[i.val]!)[c.val]!).map
    (fun row ↦ row.map (fun k ↦ wordDictionary[k]!))

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryOrbitTableData16
