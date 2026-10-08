import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleOrbits
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameDisplacementImporter
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicOrbitStabilizerRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistryChildTableData

/-! Selected invariant-state executable table accessors. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistry

abbrev Source := PrimitiveAffineEightFrameRow24ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop15TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩
abbrev ModelModule := PrimitiveAffineEightFrameRow24ModuleRepresentation.ModelModule

def child
    (i : Fin 17) (c : Fin 17) : Fin 17 :=
  SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistryChildTableData.child i c

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistry

end
