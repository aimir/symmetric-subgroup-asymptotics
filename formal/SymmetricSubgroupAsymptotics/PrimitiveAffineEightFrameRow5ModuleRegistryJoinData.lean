import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleOrbits
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameDisplacementImporter
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicOrbitStabilizerRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRegistryChildTableData

/-! Selected invariant-state executable table accessors. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRegistry

abbrev Source := PrimitiveAffineEightFrameRow5ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow5TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩
abbrev ModelModule := PrimitiveAffineEightFrameRow5ModuleRepresentation.ModelModule

def child
    (i : Fin 14) (c : Fin 14) : Fin 14 :=
  SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRegistryChildTableData.child i c

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRegistry

end
