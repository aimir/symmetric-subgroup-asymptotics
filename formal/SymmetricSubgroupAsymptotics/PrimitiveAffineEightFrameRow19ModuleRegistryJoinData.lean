import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleOrbits
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameDisplacementImporter
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicOrbitStabilizerRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistryChildTableData

/-! Selected invariant-state executable table accessors. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistry

abbrev Source := PrimitiveAffineEightFrameRow19ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop10TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩
abbrev ModelModule := PrimitiveAffineEightFrameRow19ModuleRepresentation.ModelModule

def child
    (i : Fin 12) (c : Fin 12) : Fin 12 :=
  SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistryChildTableData.child i c

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistry

end
