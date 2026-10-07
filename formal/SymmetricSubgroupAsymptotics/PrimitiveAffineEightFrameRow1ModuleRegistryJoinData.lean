import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleOrbits
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameDisplacementImporter
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicOrbitStabilizerRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryChildTableData

/-! Selected invariant-state executable table accessors. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

abbrev Source := PrimitiveAffineEightFrameRow1ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow1TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩
abbrev ModelModule := PrimitiveAffineEightFrameRow1ModuleRepresentation.ModelModule

def child
    (i : Fin 143) (c : Fin 118) : Fin 143 :=
  SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryChildTableData.child i c

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

end
