import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleRegistryJoins
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleRegistryDisplacement0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleRegistryDisplacement16
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleRegistryDisplacement32
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleRegistryDisplacement48

/-! Assembly of the checked cyclic joins and displacement chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleRegistry

local instance sourceGroupAssembly : Group Source := PrimitiveAffineEightFrameRow2TopCertificate.group
local instance sourceInhabitedAssembly : Inhabited Source := ⟨1⟩

noncomputable def displacementCharts (i : Fin 49) :
    Σ d, BinaryCoordinateSpace 16 d :=
  (if i.val < 24 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then ⟨0, D0.displacementChart⟩ else (if i.val < 2 then ⟨2, D1.displacementChart⟩ else ⟨4, D2.displacementChart⟩)) else (if i.val < 4 then ⟨4, D3.displacementChart⟩ else (if i.val < 5 then ⟨4, D4.displacementChart⟩ else ⟨4, D5.displacementChart⟩))) else (if i.val < 9 then (if i.val < 7 then ⟨5, D6.displacementChart⟩ else (if i.val < 8 then ⟨5, D7.displacementChart⟩ else ⟨5, D8.displacementChart⟩)) else (if i.val < 10 then ⟨4, D9.displacementChart⟩ else (if i.val < 11 then ⟨5, D10.displacementChart⟩ else ⟨5, D11.displacementChart⟩)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then ⟨5, D12.displacementChart⟩ else (if i.val < 14 then ⟨6, D13.displacementChart⟩ else ⟨5, D14.displacementChart⟩)) else (if i.val < 16 then ⟨5, D15.displacementChart⟩ else (if i.val < 17 then ⟨5, D16.displacementChart⟩ else ⟨6, D17.displacementChart⟩))) else (if i.val < 21 then (if i.val < 19 then ⟨6, D18.displacementChart⟩ else (if i.val < 20 then ⟨6, D19.displacementChart⟩ else ⟨6, D20.displacementChart⟩)) else (if i.val < 22 then ⟨7, D21.displacementChart⟩ else (if i.val < 23 then ⟨8, D22.displacementChart⟩ else ⟨7, D23.displacementChart⟩))))) else (if i.val < 36 then (if i.val < 30 then (if i.val < 27 then (if i.val < 25 then ⟨7, D24.displacementChart⟩ else (if i.val < 26 then ⟨6, D25.displacementChart⟩ else ⟨7, D26.displacementChart⟩)) else (if i.val < 28 then ⟨7, D27.displacementChart⟩ else (if i.val < 29 then ⟨7, D28.displacementChart⟩ else ⟨7, D29.displacementChart⟩))) else (if i.val < 33 then (if i.val < 31 then ⟨8, D30.displacementChart⟩ else (if i.val < 32 then ⟨8, D31.displacementChart⟩ else ⟨8, D32.displacementChart⟩)) else (if i.val < 34 then ⟨7, D33.displacementChart⟩ else (if i.val < 35 then ⟨7, D34.displacementChart⟩ else ⟨9, D35.displacementChart⟩)))) else (if i.val < 42 then (if i.val < 39 then (if i.val < 37 then ⟨9, D36.displacementChart⟩ else (if i.val < 38 then ⟨9, D37.displacementChart⟩ else ⟨8, D38.displacementChart⟩)) else (if i.val < 40 then ⟨8, D39.displacementChart⟩ else (if i.val < 41 then ⟨9, D40.displacementChart⟩ else ⟨9, D41.displacementChart⟩))) else (if i.val < 45 then (if i.val < 43 then ⟨9, D42.displacementChart⟩ else (if i.val < 44 then ⟨9, D43.displacementChart⟩ else ⟨9, D44.displacementChart⟩)) else (if i.val < 47 then (if i.val < 46 then ⟨9, D45.displacementChart⟩ else ⟨10, D46.displacementChart⟩) else (if i.val < 48 then ⟨14, D47.displacementChart⟩ else ⟨16, D48.displacementChart⟩))))))

noncomputable def displacementCertificate (i : Fin 49) :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow2ModuleRepresentation.representation PrimitiveAffineEightFrameRow2TopCertificate.ambient
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.states i) (displacementCharts i).2 := by
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
  · exact D27.certificate
  · exact D28.certificate
  · exact D29.certificate
  · exact D30.certificate
  · exact D31.certificate
  · exact D32.certificate
  · exact D33.certificate
  · exact D34.certificate
  · exact D35.certificate
  · exact D36.certificate
  · exact D37.certificate
  · exact D38.certificate
  · exact D39.certificate
  · exact D40.certificate
  · exact D41.certificate
  · exact D42.certificate
  · exact D43.certificate
  · exact D44.certificate
  · exact D45.certificate
  · exact D46.certificate
  · exact D47.certificate
  · exact D48.certificate

/-- Literal displacement spaces have codimension at most two in every
invariant state, while the cyclic join table is complete. -/
noncomputable def registry :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry PrimitiveAffineEightFrameRow2ModuleRepresentation.representation 2 :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry.ofBinaryCoordinateCertificates
        PrimitiveAffineEightFrameRow2ModuleRepresentation.states axes PrimitiveAffineEightFrameRow2TopCertificate.ambient
        (fun i ↦ (displacementCharts i).1)
        (fun i ↦ (displacementCharts i).2)
        displacementCertificate (by
          intro i
          rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space,
            (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts i).2.finrank]
          change (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts i).1 ≤
            (displacementCharts i).1 + 2
          rcases i with ⟨i, hi⟩
          interval_cases i <;>
            simp [PrimitiveAffineEightFrameRow2ModuleRepresentation.charts, displacementCharts])

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleRegistry

end
