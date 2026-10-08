import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleOrbits
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameDisplacementImporter
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicOrbitStabilizerRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistryChildTableData

/-! Selected invariant-state executable table accessors. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistry

abbrev Source := PrimitiveAffineEightFrameRow26ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop17TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩
abbrev ModelModule := PrimitiveAffineEightFrameRow26ModuleRepresentation.ModelModule

def child
    (i : Fin 15) (c : Fin 15) : Fin 15 :=
  SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistryChildTableData.child i c

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistry

end
