import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleRegistryJoins
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleRegistryDisplacement0

/-! Assembly of the checked cyclic joins and displacement chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleRegistry

local instance sourceGroupAssembly : Group Source := PrimitiveAffineEightFrameRow29TopCertificate.group
local instance sourceInhabitedAssembly : Inhabited Source := ⟨1⟩

noncomputable def displacementCharts (i : Fin 5) :
    Σ d, BinaryCoordinateSpace 16 d :=
  (if i.val < 2 then (if i.val < 1 then ⟨0, D0.displacementChart⟩ else ⟨8, D1.displacementChart⟩) else (if i.val < 3 then ⟨8, D2.displacementChart⟩ else (if i.val < 4 then ⟨8, D3.displacementChart⟩ else ⟨16, D4.displacementChart⟩)))

noncomputable def displacementCertificate (i : Fin 5) :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow29ModuleRepresentation.representation PrimitiveAffineEightFrameRow29TopCertificate.ambient
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.states i) (displacementCharts i).2 := by
  rcases i with ⟨i, hi⟩
  interval_cases i
  · exact D0.certificate
  · exact D1.certificate
  · exact D2.certificate
  · exact D3.certificate
  · exact D4.certificate

/-- Literal displacement spaces have codimension at most two in every
invariant state, while the cyclic join table is complete. -/
noncomputable def registry :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry PrimitiveAffineEightFrameRow29ModuleRepresentation.representation 2 :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry.ofBinaryCoordinateCertificates
        PrimitiveAffineEightFrameRow29ModuleRepresentation.states axes PrimitiveAffineEightFrameRow29TopCertificate.ambient
        (fun i ↦ (displacementCharts i).1)
        (fun i ↦ (displacementCharts i).2)
        displacementCertificate (by
          intro i
          rw [PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space,
            (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts i).2.finrank]
          change (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts i).1 ≤
            (displacementCharts i).1 + 2
          rcases i with ⟨i, hi⟩
          interval_cases i <;>
            simp [PrimitiveAffineEightFrameRow29ModuleRepresentation.charts, displacementCharts])

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleRegistry

end
