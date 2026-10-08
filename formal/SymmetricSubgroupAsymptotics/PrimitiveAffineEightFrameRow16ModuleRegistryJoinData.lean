import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleOrbits
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameDisplacementImporter
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicOrbitStabilizerRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistryChildTableData

/-! Selected invariant-state executable table accessors. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistry

abbrev Source := PrimitiveAffineEightFrameRow16ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩
abbrev ModelModule := PrimitiveAffineEightFrameRow16ModuleRepresentation.ModelModule

def child
    (i : Fin 7) (c : Fin 7) : Fin 7 :=
  SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistryChildTableData.child i c

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistry

end
