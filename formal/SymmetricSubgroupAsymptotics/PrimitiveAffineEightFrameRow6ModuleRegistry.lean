import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryJoins
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryDisplacement0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryDisplacement8
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryDisplacement16

/-! Assembly of the checked cyclic joins and displacement chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistry

local instance sourceGroupAssembly : Group Source := PrimitiveAffineEightFrameRow6TopCertificate.group
local instance sourceInhabitedAssembly : Inhabited Source := ⟨1⟩

noncomputable def displacementCharts (i : Fin 17) :
    Σ d, BinaryCoordinateSpace 16 d :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ⟨0, D0.displacementChart⟩ else ⟨4, D1.displacementChart⟩) else (if i.val < 3 then ⟨6, D2.displacementChart⟩ else ⟨6, D3.displacementChart⟩)) else (if i.val < 6 then (if i.val < 5 then ⟨6, D4.displacementChart⟩ else ⟨6, D5.displacementChart⟩) else (if i.val < 7 then ⟨8, D6.displacementChart⟩ else ⟨8, D7.displacementChart⟩))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then ⟨8, D8.displacementChart⟩ else ⟨8, D9.displacementChart⟩) else (if i.val < 11 then ⟨8, D10.displacementChart⟩ else ⟨10, D11.displacementChart⟩)) else (if i.val < 14 then (if i.val < 13 then ⟨10, D12.displacementChart⟩ else ⟨10, D13.displacementChart⟩) else (if i.val < 15 then ⟨10, D14.displacementChart⟩ else (if i.val < 16 then ⟨12, D15.displacementChart⟩ else ⟨16, D16.displacementChart⟩)))))

noncomputable def displacementCertificate (i : Fin 17) :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow6ModuleRepresentation.representation PrimitiveAffineEightFrameRow6TopCertificate.ambient
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states i) (displacementCharts i).2 := by
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
  · exact D14.certificate
  · exact D15.certificate
  · exact D16.certificate

/-- Literal displacement spaces have codimension at most two in every
invariant state, while the cyclic join table is complete. -/
noncomputable def registry :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry PrimitiveAffineEightFrameRow6ModuleRepresentation.representation 2 :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry.ofBinaryCoordinateCertificates
        PrimitiveAffineEightFrameRow6ModuleRepresentation.states axes PrimitiveAffineEightFrameRow6TopCertificate.ambient
        (fun i ↦ (displacementCharts i).1)
        (fun i ↦ (displacementCharts i).2)
        displacementCertificate (by
          intro i
          rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space,
            (PrimitiveAffineEightFrameRow6ModuleRepresentation.charts i).2.finrank]
          change (PrimitiveAffineEightFrameRow6ModuleRepresentation.charts i).1 ≤
            (displacementCharts i).1 + 2
          rcases i with ⟨i, hi⟩
          interval_cases i <;>
            simp [PrimitiveAffineEightFrameRow6ModuleRepresentation.charts, displacementCharts])

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistry

end
