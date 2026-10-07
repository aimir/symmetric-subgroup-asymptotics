import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleOrbits
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameDisplacementImporter
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicOrbitStabilizerRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleRegistryChildTableData

/-! Selected invariant-state executable table accessors. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleRegistry

abbrev Source := PrimitiveAffineEightFrameRow4ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow4TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩
abbrev ModelModule := PrimitiveAffineEightFrameRow4ModuleRepresentation.ModelModule

def child
    (i : Fin 14) (c : Fin 14) : Fin 14 :=
  SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleRegistryChildTableData.child i c

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleRegistry

end
