import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryJoins
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryDisplacement0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryDisplacement8
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryDisplacement16
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryDisplacement24

/-! Assembly of the checked cyclic joins and displacement chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistry

local instance sourceGroupAssembly : Group Source := PrimitiveAffineEightFrameRow9TopCertificate.group
local instance sourceInhabitedAssembly : Inhabited Source := ⟨1⟩

noncomputable def displacementCharts (i : Fin 25) :
    Σ d, BinaryCoordinateSpace 16 d :=
  (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then ⟨0, D0.displacementChart⟩ else (if i.val < 2 then ⟨2, D1.displacementChart⟩ else ⟨4, D2.displacementChart⟩)) else (if i.val < 4 then ⟨4, D3.displacementChart⟩ else (if i.val < 5 then ⟨5, D4.displacementChart⟩ else ⟨6, D5.displacementChart⟩))) else (if i.val < 9 then (if i.val < 7 then ⟨5, D6.displacementChart⟩ else (if i.val < 8 then ⟨5, D7.displacementChart⟩ else ⟨5, D8.displacementChart⟩)) else (if i.val < 10 then ⟨6, D9.displacementChart⟩ else (if i.val < 11 then ⟨8, D10.displacementChart⟩ else ⟨7, D11.displacementChart⟩)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then ⟨7, D12.displacementChart⟩ else (if i.val < 14 then ⟨7, D13.displacementChart⟩ else ⟨7, D14.displacementChart⟩)) else (if i.val < 16 then ⟨8, D15.displacementChart⟩ else (if i.val < 17 then ⟨7, D16.displacementChart⟩ else ⟨9, D17.displacementChart⟩))) else (if i.val < 21 then (if i.val < 19 then ⟨9, D18.displacementChart⟩ else (if i.val < 20 then ⟨9, D19.displacementChart⟩ else ⟨9, D20.displacementChart⟩)) else (if i.val < 23 then (if i.val < 22 then ⟨9, D21.displacementChart⟩ else ⟨11, D22.displacementChart⟩) else (if i.val < 24 then ⟨14, D23.displacementChart⟩ else ⟨16, D24.displacementChart⟩)))))

noncomputable def displacementCertificate (i : Fin 25) :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow9ModuleRepresentation.representation PrimitiveAffineEightFrameRow9TopCertificate.ambient
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states i) (displacementCharts i).2 := by
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

/-- Literal displacement spaces have codimension at most two in every
invariant state, while the cyclic join table is complete. -/
noncomputable def registry :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry PrimitiveAffineEightFrameRow9ModuleRepresentation.representation 2 :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry.ofBinaryCoordinateCertificates
        PrimitiveAffineEightFrameRow9ModuleRepresentation.states axes PrimitiveAffineEightFrameRow9TopCertificate.ambient
        (fun i ↦ (displacementCharts i).1)
        (fun i ↦ (displacementCharts i).2)
        displacementCertificate (by
          intro i
          rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space,
            (PrimitiveAffineEightFrameRow9ModuleRepresentation.charts i).2.finrank]
          change (PrimitiveAffineEightFrameRow9ModuleRepresentation.charts i).1 ≤
            (displacementCharts i).1 + 2
          rcases i with ⟨i, hi⟩
          interval_cases i <;>
            simp [PrimitiveAffineEightFrameRow9ModuleRepresentation.charts, displacementCharts])

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistry

end
