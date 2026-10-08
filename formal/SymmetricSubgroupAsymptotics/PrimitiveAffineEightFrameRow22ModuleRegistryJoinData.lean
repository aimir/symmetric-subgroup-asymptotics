import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleOrbits
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameDisplacementImporter
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicOrbitStabilizerRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistryChildTableData

/-! Selected invariant-state executable table accessors. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistry

abbrev Source := PrimitiveAffineEightFrameRow22ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop13TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩
abbrev ModelModule := PrimitiveAffineEightFrameRow22ModuleRepresentation.ModelModule

def child
    (i : Fin 23) (c : Fin 19) : Fin 23 :=
  SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistryChildTableData.child i c

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistry

end
