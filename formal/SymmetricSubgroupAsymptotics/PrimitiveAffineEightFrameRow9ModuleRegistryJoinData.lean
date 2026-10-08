import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleOrbits
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameDisplacementImporter
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicOrbitStabilizerRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryChildTableData

/-! Selected invariant-state executable table accessors. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistry

abbrev Source := PrimitiveAffineEightFrameRow9ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow9TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩
abbrev ModelModule := PrimitiveAffineEightFrameRow9ModuleRepresentation.ModelModule

def child
    (i : Fin 25) (c : Fin 22) : Fin 25 :=
  SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryChildTableData.child i c

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistry

end
