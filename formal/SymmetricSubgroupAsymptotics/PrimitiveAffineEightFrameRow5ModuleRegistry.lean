import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRegistryJoins
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRegistryDisplacement0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRegistryDisplacement8

/-! Assembly of the checked cyclic joins and displacement chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRegistry

local instance sourceGroupAssembly : Group Source := PrimitiveAffineEightFrameRow5TopCertificate.group
local instance sourceInhabitedAssembly : Inhabited Source := ⟨1⟩

noncomputable def displacementCharts (i : Fin 14) :
    Σ d, BinaryCoordinateSpace 16 d :=
  (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then ⟨0, D0.displacementChart⟩ else (if i.val < 2 then ⟨2, D1.displacementChart⟩ else ⟨2, D2.displacementChart⟩)) else (if i.val < 5 then (if i.val < 4 then ⟨2, D3.displacementChart⟩ else ⟨4, D4.displacementChart⟩) else (if i.val < 6 then ⟨6, D5.displacementChart⟩ else ⟨8, D6.displacementChart⟩))) else (if i.val < 10 then (if i.val < 8 then ⟨8, D7.displacementChart⟩ else (if i.val < 9 then ⟨10, D8.displacementChart⟩ else ⟨12, D9.displacementChart⟩)) else (if i.val < 12 then (if i.val < 11 then ⟨14, D10.displacementChart⟩ else ⟨14, D11.displacementChart⟩) else (if i.val < 13 then ⟨14, D12.displacementChart⟩ else ⟨16, D13.displacementChart⟩))))

noncomputable def displacementCertificate (i : Fin 14) :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow5ModuleRepresentation.representation PrimitiveAffineEightFrameRow5TopCertificate.ambient
      (PrimitiveAffineEightFrameRow5ModuleRepresentation.states i) (displacementCharts i).2 := by
  rcases i with ⟨i, hi⟩
  interval_cases i
  · exact D0.certificate
  · exact D1.certificate
  · exact D2.certificate
  · exact D3.certificate
  · exact D4.certificate
  · exact D5.certificate
  · exact D6.certificate
  · exact D7.certificate
  · exact D8.certificate
  · exact D9.certificate
  · exact D10.certificate
  · exact D11.certificate
  · exact D12.certificate
  · exact D13.certificate

/-- Literal displacement spaces have codimension at most two in every
invariant state, while the cyclic join table is complete. -/
noncomputable def registry :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry PrimitiveAffineEightFrameRow5ModuleRepresentation.representation 2 :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry.ofBinaryCoordinateCertificates
        PrimitiveAffineEightFrameRow5ModuleRepresentation.states axes PrimitiveAffineEightFrameRow5TopCertificate.ambient
        (fun i ↦ (displacementCharts i).1)
        (fun i ↦ (displacementCharts i).2)
        displacementCertificate (by
          intro i
          rw [PrimitiveAffineEightFrameRow5ModuleRepresentation.states_space,
            (PrimitiveAffineEightFrameRow5ModuleRepresentation.charts i).2.finrank]
          change (PrimitiveAffineEightFrameRow5ModuleRepresentation.charts i).1 ≤
            (displacementCharts i).1 + 2
          rcases i with ⟨i, hi⟩
          interval_cases i <;>
            simp [PrimitiveAffineEightFrameRow5ModuleRepresentation.charts, displacementCharts])

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow5ModuleRegistry

end
