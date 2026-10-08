import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleOrbits
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameDisplacementImporter
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicOrbitStabilizerRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistryChildTableData

/-! Selected invariant-state executable table accessors. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistry

abbrev Source := PrimitiveAffineEightFrameRow12ModuleRepresentation.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop8TopCertificate.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩
abbrev ModelModule := PrimitiveAffineEightFrameRow12ModuleRepresentation.ModelModule

def child
    (i : Fin 11) (c : Fin 11) : Fin 11 :=
  SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistryChildTableData.child i c

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistry

end
