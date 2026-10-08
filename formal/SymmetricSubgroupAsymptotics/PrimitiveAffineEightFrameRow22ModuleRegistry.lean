import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistryJoins
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistryDisplacement0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistryDisplacement8
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistryDisplacement16

/-! Assembly of the checked cyclic joins and displacement chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistry

local instance sourceGroupAssembly : Group Source := PrimitiveAffineEightFrameTop13TopCertificate.group
local instance sourceInhabitedAssembly : Inhabited Source := ⟨1⟩

noncomputable def displacementCharts (i : Fin 23) :
    Σ d, BinaryCoordinateSpace 16 d :=
  (if i.val < 11 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then ⟨0, D0.displacementChart⟩ else ⟨2, D1.displacementChart⟩) else (if i.val < 3 then ⟨2, D2.displacementChart⟩ else (if i.val < 4 then ⟨2, D3.displacementChart⟩ else ⟨2, D4.displacementChart⟩))) else (if i.val < 8 then (if i.val < 6 then ⟨2, D5.displacementChart⟩ else (if i.val < 7 then ⟨4, D6.displacementChart⟩ else ⟨4, D7.displacementChart⟩)) else (if i.val < 9 then ⟨4, D8.displacementChart⟩ else (if i.val < 10 then ⟨4, D9.displacementChart⟩ else ⟨4, D10.displacementChart⟩)))) else (if i.val < 17 then (if i.val < 14 then (if i.val < 12 then ⟨8, D11.displacementChart⟩ else (if i.val < 13 then ⟨10, D12.displacementChart⟩ else ⟨10, D13.displacementChart⟩)) else (if i.val < 15 then ⟨10, D14.displacementChart⟩ else (if i.val < 16 then ⟨10, D15.displacementChart⟩ else ⟨10, D16.displacementChart⟩))) else (if i.val < 20 then (if i.val < 18 then ⟨12, D17.displacementChart⟩ else (if i.val < 19 then ⟨12, D18.displacementChart⟩ else ⟨12, D19.displacementChart⟩)) else (if i.val < 21 then ⟨12, D20.displacementChart⟩ else (if i.val < 22 then ⟨12, D21.displacementChart⟩ else ⟨16, D22.displacementChart⟩)))))

noncomputable def displacementCertificate (i : Fin 23) :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow22ModuleRepresentation.representation PrimitiveAffineEightFrameTop13TopCertificate.ambient
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states i) (displacementCharts i).2 := by
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

/-- Literal displacement spaces have codimension at most two in every
invariant state, while the cyclic join table is complete. -/
noncomputable def registry :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry PrimitiveAffineEightFrameRow22ModuleRepresentation.representation 2 :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry.ofBinaryCoordinateCertificates
        PrimitiveAffineEightFrameRow22ModuleRepresentation.states axes PrimitiveAffineEightFrameTop13TopCertificate.ambient
        (fun i ↦ (displacementCharts i).1)
        (fun i ↦ (displacementCharts i).2)
        displacementCertificate (by
          intro i
          rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space,
            (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts i).2.finrank]
          change (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts i).1 ≤
            (displacementCharts i).1 + 2
          rcases i with ⟨i, hi⟩
          interval_cases i <;>
            simp [PrimitiveAffineEightFrameRow22ModuleRepresentation.charts, displacementCharts])

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistry

end
