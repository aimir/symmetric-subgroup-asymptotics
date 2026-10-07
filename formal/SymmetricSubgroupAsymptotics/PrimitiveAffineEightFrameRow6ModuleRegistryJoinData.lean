import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleOrbits
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameDisplacementImporter
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicOrbitStabilizerRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryChildTableData

/-! Selected invariant-state executable table accessors. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistry

abbrev Source := PrimitiveAffineEightFrameRow6ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow6TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩
abbrev ModelModule := PrimitiveAffineEightFrameRow6ModuleRepresentation.ModelModule

def child
    (i : Fin 17) (c : Fin 17) : Fin 17 :=
  SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryChildTableData.child i c

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistry

end
