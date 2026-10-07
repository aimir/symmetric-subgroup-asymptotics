import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleOrbits
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameDisplacementImporter
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicOrbitStabilizerRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleRegistryChildTableData

/-! Selected invariant-state executable table accessors. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleRegistry

abbrev Source := PrimitiveAffineEightFrameRow7ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow7TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩
abbrev ModelModule := PrimitiveAffineEightFrameRow7ModuleRepresentation.ModelModule

def child
    (i : Fin 32) (c : Fin 22) : Fin 32 :=
  SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleRegistryChildTableData.child i c

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleRegistry

end
