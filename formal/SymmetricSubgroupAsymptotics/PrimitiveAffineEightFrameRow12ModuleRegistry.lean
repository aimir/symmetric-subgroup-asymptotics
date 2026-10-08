import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistryJoins
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistryDisplacement0

/-! Assembly of the checked cyclic joins and displacement chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistry

local instance sourceGroupAssembly : Group Source := PrimitiveAffineEightFrameTop8TopCertificate.group
local instance sourceInhabitedAssembly : Inhabited Source := ⟨1⟩

noncomputable def displacementCharts (i : Fin 11) :
    Σ d, BinaryCoordinateSpace 16 d :=
  (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then ⟨0, D0.displacementChart⟩ else ⟨4, D1.displacementChart⟩) else (if i.val < 3 then ⟨6, D2.displacementChart⟩ else (if i.val < 4 then ⟨6, D3.displacementChart⟩ else ⟨8, D4.displacementChart⟩))) else (if i.val < 8 then (if i.val < 6 then ⟨8, D5.displacementChart⟩ else (if i.val < 7 then ⟨8, D6.displacementChart⟩ else ⟨10, D7.displacementChart⟩)) else (if i.val < 9 then ⟨10, D8.displacementChart⟩ else (if i.val < 10 then ⟨12, D9.displacementChart⟩ else ⟨16, D10.displacementChart⟩))))

noncomputable def displacementCertificate (i : Fin 11) :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow12ModuleRepresentation.representation PrimitiveAffineEightFrameTop8TopCertificate.ambient
      (PrimitiveAffineEightFrameRow12ModuleRepresentation.states i) (displacementCharts i).2 := by
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

/-- Literal displacement spaces have codimension at most two in every
invariant state, while the cyclic join table is complete. -/
noncomputable def registry :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry PrimitiveAffineEightFrameRow12ModuleRepresentation.representation 2 :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry.ofBinaryCoordinateCertificates
        PrimitiveAffineEightFrameRow12ModuleRepresentation.states axes PrimitiveAffineEightFrameTop8TopCertificate.ambient
        (fun i ↦ (displacementCharts i).1)
        (fun i ↦ (displacementCharts i).2)
        displacementCertificate (by
          intro i
          rw [PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space,
            (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts i).2.finrank]
          change (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts i).1 ≤
            (displacementCharts i).1 + 2
          rcases i with ⟨i, hi⟩
          interval_cases i <;>
            simp [PrimitiveAffineEightFrameRow12ModuleRepresentation.charts, displacementCharts])

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistry

end
