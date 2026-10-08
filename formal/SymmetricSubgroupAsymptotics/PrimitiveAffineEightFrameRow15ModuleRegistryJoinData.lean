import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleOrbits
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameDisplacementImporter
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicOrbitStabilizerRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistryChildTableData

/-! Selected invariant-state executable table accessors. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistry

abbrev Source := PrimitiveAffineEightFrameRow15ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩
abbrev ModelModule := PrimitiveAffineEightFrameRow15ModuleRepresentation.ModelModule

def child
    (i : Fin 6) (c : Fin 6) : Fin 6 :=
  SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistryChildTableData.child i c

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistry

end
