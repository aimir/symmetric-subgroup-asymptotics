import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleRegistryJoins
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleRegistryDisplacement0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleRegistryDisplacement16

/-! Assembly of the checked cyclic joins and displacement chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleRegistry

local instance sourceGroupAssembly : Group Source := PrimitiveAffineEightFrameRow23TopCertificate.group
local instance sourceInhabitedAssembly : Inhabited Source := ⟨1⟩

noncomputable def displacementCharts (i : Fin 27) :
    Σ d, BinaryCoordinateSpace 16 d :=
  (if i.val < 13 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then ⟨0, D0.displacementChart⟩ else (if i.val < 2 then ⟨2, D1.displacementChart⟩ else ⟨2, D2.displacementChart⟩)) else (if i.val < 4 then ⟨4, D3.displacementChart⟩ else (if i.val < 5 then ⟨3, D4.displacementChart⟩ else ⟨4, D5.displacementChart⟩))) else (if i.val < 9 then (if i.val < 7 then ⟨5, D6.displacementChart⟩ else (if i.val < 8 then ⟨6, D7.displacementChart⟩ else ⟨6, D8.displacementChart⟩)) else (if i.val < 11 then (if i.val < 10 then ⟨6, D9.displacementChart⟩ else ⟨6, D10.displacementChart⟩) else (if i.val < 12 then ⟨6, D11.displacementChart⟩ else ⟨8, D12.displacementChart⟩)))) else (if i.val < 20 then (if i.val < 16 then (if i.val < 14 then ⟨8, D13.displacementChart⟩ else (if i.val < 15 then ⟨7, D14.displacementChart⟩ else ⟨8, D15.displacementChart⟩)) else (if i.val < 18 then (if i.val < 17 then ⟨9, D16.displacementChart⟩ else ⟨10, D17.displacementChart⟩) else (if i.val < 19 then ⟨10, D18.displacementChart⟩ else ⟨9, D19.displacementChart⟩))) else (if i.val < 23 then (if i.val < 21 then ⟨9, D20.displacementChart⟩ else (if i.val < 22 then ⟨10, D21.displacementChart⟩ else ⟨12, D22.displacementChart⟩)) else (if i.val < 25 then (if i.val < 24 then ⟨11, D23.displacementChart⟩ else ⟨12, D24.displacementChart⟩) else (if i.val < 26 then ⟨13, D25.displacementChart⟩ else ⟨16, D26.displacementChart⟩)))))

noncomputable def displacementCertificate (i : Fin 27) :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow23ModuleRepresentation.representation PrimitiveAffineEightFrameRow23TopCertificate.ambient
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states i) (displacementCharts i).2 := by
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
  · exact D17.certificate
  · exact D18.certificate
  · exact D19.certificate
  · exact D20.certificate
  · exact D21.certificate
  · exact D22.certificate
  · exact D23.certificate
  · exact D24.certificate
  · exact D25.certificate
  · exact D26.certificate

/-- Literal displacement spaces have codimension at most two in every
invariant state, while the cyclic join table is complete. -/
noncomputable def registry :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry PrimitiveAffineEightFrameRow23ModuleRepresentation.representation 2 :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry.ofBinaryCoordinateCertificates
        PrimitiveAffineEightFrameRow23ModuleRepresentation.states axes PrimitiveAffineEightFrameRow23TopCertificate.ambient
        (fun i ↦ (displacementCharts i).1)
        (fun i ↦ (displacementCharts i).2)
        displacementCertificate (by
          intro i
          rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space,
            (PrimitiveAffineEightFrameRow23ModuleRepresentation.charts i).2.finrank]
          change (PrimitiveAffineEightFrameRow23ModuleRepresentation.charts i).1 ≤
            (displacementCharts i).1 + 2
          rcases i with ⟨i, hi⟩
          interval_cases i <;>
            simp [PrimitiveAffineEightFrameRow23ModuleRepresentation.charts, displacementCharts])

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleRegistry

end
