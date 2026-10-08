import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleOrbits

/-! Executable orbit-word table for states 16–16. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistryOrbitTableData16

abbrev Source := PrimitiveAffineEightFrameRow24ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop15TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩

private def wordDictionary : Array Source :=
  #[PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [3,3],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [3,3,3],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [4,3],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [3,4],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [3,4,3],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [3,3,4],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [1],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [2],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [0,4],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [1,4],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [2,4],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [0],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [0,4,3],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [0,3],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [1,3],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [1,3,3],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [0,3,3],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [0,3,3,3],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [2,3],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [0,3,4],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [0,4,3,3],PrimitiveAffineEightFrameRow24ModuleOrbits.sourceWord [0,3,3,4]]

private def childOrbitTable : Array (Array (Array (List ℕ))) :=
  #[#[#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]]]

def childOrbitRows (i : Fin 1) (c : Fin 17) : Array (List Source) :=
  ((childOrbitTable[i.val]!)[c.val]!).map
    (fun row ↦ row.map (fun k ↦ wordDictionary[k]!))

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistryOrbitTableData16
