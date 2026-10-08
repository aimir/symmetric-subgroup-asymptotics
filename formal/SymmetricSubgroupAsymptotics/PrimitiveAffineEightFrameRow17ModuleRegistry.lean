import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistryJoins
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistryDisplacement0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistryDisplacement8

/-! Assembly of the checked cyclic joins and displacement chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistry

local instance sourceGroupAssembly : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group
local instance sourceInhabitedAssembly : Inhabited Source := ⟨1⟩

noncomputable def displacementCharts (i : Fin 12) :
    Σ d, BinaryCoordinateSpace 16 d :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then ⟨0, D0.displacementChart⟩ else (if i.val < 2 then ⟨4, D1.displacementChart⟩ else ⟨4, D2.displacementChart⟩)) else (if i.val < 4 then ⟨5, D3.displacementChart⟩ else (if i.val < 5 then ⟨6, D4.displacementChart⟩ else ⟨8, D5.displacementChart⟩))) else (if i.val < 9 then (if i.val < 7 then ⟨7, D6.displacementChart⟩ else (if i.val < 8 then ⟨8, D7.displacementChart⟩ else ⟨9, D8.displacementChart⟩)) else (if i.val < 10 then ⟨10, D9.displacementChart⟩ else (if i.val < 11 then ⟨11, D10.displacementChart⟩ else ⟨16, D11.displacementChart⟩))))

noncomputable def displacementCertificate (i : Fin 12) :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow17ModuleRepresentation.representation PrimitiveAffineEightFrameTop9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states i) (displacementCharts i).2 := by
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

/-- Literal displacement spaces have codimension at most two in every
invariant state, while the cyclic join table is complete. -/
noncomputable def registry :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry PrimitiveAffineEightFrameRow17ModuleRepresentation.representation 2 :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry.ofBinaryCoordinateCertificates
        PrimitiveAffineEightFrameRow17ModuleRepresentation.states axes PrimitiveAffineEightFrameTop9TopCertificate.ambient
        (fun i ↦ (displacementCharts i).1)
        (fun i ↦ (displacementCharts i).2)
        displacementCertificate (by
          intro i
          rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space,
            (PrimitiveAffineEightFrameRow17ModuleRepresentation.charts i).2.finrank]
          change (PrimitiveAffineEightFrameRow17ModuleRepresentation.charts i).1 ≤
            (displacementCharts i).1 + 2
          rcases i with ⟨i, hi⟩
          interval_cases i <;>
            simp [PrimitiveAffineEightFrameRow17ModuleRepresentation.charts, displacementCharts])

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistry

end
