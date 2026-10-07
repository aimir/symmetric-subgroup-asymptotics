import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoins
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryDisplacement0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryDisplacement8
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryDisplacement16
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryDisplacement24
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryDisplacement32
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryDisplacement40
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryDisplacement48
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryDisplacement56
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryDisplacement64
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryDisplacement72
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryDisplacement80
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryDisplacement88
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryDisplacement96

/-! Assembly of the checked cyclic joins and displacement chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

local instance sourceGroupAssembly : Group Source := PrimitiveAffineEightFrameRow0TopCertificate.group
local instance sourceInhabitedAssembly : Inhabited Source := ⟨1⟩

noncomputable def displacementCharts (i : Fin 101) :
    Σ d, BinaryCoordinateSpace 16 d :=
  (if i.val < 50 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then ⟨0, D0.displacementChart⟩ else (if i.val < 2 then ⟨2, D1.displacementChart⟩ else ⟨2, D2.displacementChart⟩)) else (if i.val < 4 then ⟨2, D3.displacementChart⟩ else (if i.val < 5 then ⟨2, D4.displacementChart⟩ else ⟨4, D5.displacementChart⟩))) else (if i.val < 9 then (if i.val < 7 then ⟨2, D6.displacementChart⟩ else (if i.val < 8 then ⟨4, D7.displacementChart⟩ else ⟨4, D8.displacementChart⟩)) else (if i.val < 10 then ⟨4, D9.displacementChart⟩ else (if i.val < 11 then ⟨4, D10.displacementChart⟩ else ⟨4, D11.displacementChart⟩)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then ⟨4, D12.displacementChart⟩ else (if i.val < 14 then ⟨4, D13.displacementChart⟩ else ⟨4, D14.displacementChart⟩)) else (if i.val < 16 then ⟨4, D15.displacementChart⟩ else (if i.val < 17 then ⟨4, D16.displacementChart⟩ else ⟨4, D17.displacementChart⟩))) else (if i.val < 21 then (if i.val < 19 then ⟨4, D18.displacementChart⟩ else (if i.val < 20 then ⟨4, D19.displacementChart⟩ else ⟨4, D20.displacementChart⟩)) else (if i.val < 23 then (if i.val < 22 then ⟨4, D21.displacementChart⟩ else ⟨4, D22.displacementChart⟩) else (if i.val < 24 then ⟨4, D23.displacementChart⟩ else ⟨4, D24.displacementChart⟩))))) else (if i.val < 37 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then ⟨4, D25.displacementChart⟩ else (if i.val < 27 then ⟨5, D26.displacementChart⟩ else ⟨5, D27.displacementChart⟩)) else (if i.val < 29 then ⟨5, D28.displacementChart⟩ else (if i.val < 30 then ⟨4, D29.displacementChart⟩ else ⟨5, D30.displacementChart⟩))) else (if i.val < 34 then (if i.val < 32 then ⟨5, D31.displacementChart⟩ else (if i.val < 33 then ⟨5, D32.displacementChart⟩ else ⟨6, D33.displacementChart⟩)) else (if i.val < 35 then ⟨4, D34.displacementChart⟩ else (if i.val < 36 then ⟨4, D35.displacementChart⟩ else ⟨4, D36.displacementChart⟩)))) else (if i.val < 43 then (if i.val < 40 then (if i.val < 38 then ⟨4, D37.displacementChart⟩ else (if i.val < 39 then ⟨5, D38.displacementChart⟩ else ⟨5, D39.displacementChart⟩)) else (if i.val < 41 then ⟨5, D40.displacementChart⟩ else (if i.val < 42 then ⟨6, D41.displacementChart⟩ else ⟨6, D42.displacementChart⟩))) else (if i.val < 46 then (if i.val < 44 then ⟨6, D43.displacementChart⟩ else (if i.val < 45 then ⟨6, D44.displacementChart⟩ else ⟨7, D45.displacementChart⟩)) else (if i.val < 48 then (if i.val < 47 then ⟨8, D46.displacementChart⟩ else ⟨7, D47.displacementChart⟩) else (if i.val < 49 then ⟨7, D48.displacementChart⟩ else ⟨6, D49.displacementChart⟩)))))) else (if i.val < 75 then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if i.val < 51 then ⟨7, D50.displacementChart⟩ else (if i.val < 52 then ⟨7, D51.displacementChart⟩ else ⟨7, D52.displacementChart⟩)) else (if i.val < 54 then ⟨8, D53.displacementChart⟩ else (if i.val < 55 then ⟨8, D54.displacementChart⟩ else ⟨8, D55.displacementChart⟩))) else (if i.val < 59 then (if i.val < 57 then ⟨8, D56.displacementChart⟩ else (if i.val < 58 then ⟨7, D57.displacementChart⟩ else ⟨8, D58.displacementChart⟩)) else (if i.val < 60 then ⟨8, D59.displacementChart⟩ else (if i.val < 61 then ⟨8, D60.displacementChart⟩ else ⟨7, D61.displacementChart⟩)))) else (if i.val < 68 then (if i.val < 65 then (if i.val < 63 then ⟨7, D62.displacementChart⟩ else (if i.val < 64 then ⟨9, D63.displacementChart⟩ else ⟨9, D64.displacementChart⟩)) else (if i.val < 66 then ⟨9, D65.displacementChart⟩ else (if i.val < 67 then ⟨8, D66.displacementChart⟩ else ⟨8, D67.displacementChart⟩))) else (if i.val < 71 then (if i.val < 69 then ⟨9, D68.displacementChart⟩ else (if i.val < 70 then ⟨9, D69.displacementChart⟩ else ⟨9, D70.displacementChart⟩)) else (if i.val < 73 then (if i.val < 72 then ⟨10, D71.displacementChart⟩ else ⟨10, D72.displacementChart⟩) else (if i.val < 74 then ⟨10, D73.displacementChart⟩ else ⟨10, D74.displacementChart⟩))))) else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then (if i.val < 76 then ⟨9, D75.displacementChart⟩ else (if i.val < 77 then ⟨9, D76.displacementChart⟩ else ⟨9, D77.displacementChart⟩)) else (if i.val < 79 then ⟨10, D78.displacementChart⟩ else (if i.val < 80 then ⟨10, D79.displacementChart⟩ else ⟨10, D80.displacementChart⟩))) else (if i.val < 84 then (if i.val < 82 then ⟨10, D81.displacementChart⟩ else (if i.val < 83 then ⟨10, D82.displacementChart⟩ else ⟨10, D83.displacementChart⟩)) else (if i.val < 86 then (if i.val < 85 then ⟨10, D84.displacementChart⟩ else ⟨10, D85.displacementChart⟩) else (if i.val < 87 then ⟨10, D86.displacementChart⟩ else ⟨10, D87.displacementChart⟩)))) else (if i.val < 94 then (if i.val < 91 then (if i.val < 89 then ⟨10, D88.displacementChart⟩ else (if i.val < 90 then ⟨10, D89.displacementChart⟩ else ⟨10, D90.displacementChart⟩)) else (if i.val < 92 then ⟨10, D91.displacementChart⟩ else (if i.val < 93 then ⟨10, D92.displacementChart⟩ else ⟨10, D93.displacementChart⟩))) else (if i.val < 97 then (if i.val < 95 then ⟨10, D94.displacementChart⟩ else (if i.val < 96 then ⟨12, D95.displacementChart⟩ else ⟨12, D96.displacementChart⟩)) else (if i.val < 99 then (if i.val < 98 then ⟨12, D97.displacementChart⟩ else ⟨12, D98.displacementChart⟩) else (if i.val < 100 then ⟨12, D99.displacementChart⟩ else ⟨16, D100.displacementChart⟩)))))))

noncomputable def displacementCertificate (i : Fin 101) :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow0ModuleRepresentation.representation PrimitiveAffineEightFrameRow0TopCertificate.ambient
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states i) (displacementCharts i).2 := by
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
  · exact D49.certificate
  · exact D50.certificate
  · exact D51.certificate
  · exact D52.certificate
  · exact D53.certificate
  · exact D54.certificate
  · exact D55.certificate
  · exact D56.certificate
  · exact D57.certificate
  · exact D58.certificate
  · exact D59.certificate
  · exact D60.certificate
  · exact D61.certificate
  · exact D62.certificate
  · exact D63.certificate
  · exact D64.certificate
  · exact D65.certificate
  · exact D66.certificate
  · exact D67.certificate
  · exact D68.certificate
  · exact D69.certificate
  · exact D70.certificate
  · exact D71.certificate
  · exact D72.certificate
  · exact D73.certificate
  · exact D74.certificate
  · exact D75.certificate
  · exact D76.certificate
  · exact D77.certificate
  · exact D78.certificate
  · exact D79.certificate
  · exact D80.certificate
  · exact D81.certificate
  · exact D82.certificate
  · exact D83.certificate
  · exact D84.certificate
  · exact D85.certificate
  · exact D86.certificate
  · exact D87.certificate
  · exact D88.certificate
  · exact D89.certificate
  · exact D90.certificate
  · exact D91.certificate
  · exact D92.certificate
  · exact D93.certificate
  · exact D94.certificate
  · exact D95.certificate
  · exact D96.certificate
  · exact D97.certificate
  · exact D98.certificate
  · exact D99.certificate
  · exact D100.certificate

/-- Literal displacement spaces have codimension at most two in every
invariant state, while the cyclic join table is complete. -/
noncomputable def registry :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry PrimitiveAffineEightFrameRow0ModuleRepresentation.representation 2 :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry.ofBinaryCoordinateCertificates
        PrimitiveAffineEightFrameRow0ModuleRepresentation.states axes PrimitiveAffineEightFrameRow0TopCertificate.ambient
        (fun i ↦ (displacementCharts i).1)
        (fun i ↦ (displacementCharts i).2)
        displacementCertificate (by
          intro i
          rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space,
            (PrimitiveAffineEightFrameRow0ModuleRepresentation.charts i).2.finrank]
          change (PrimitiveAffineEightFrameRow0ModuleRepresentation.charts i).1 ≤
            (displacementCharts i).1 + 2
          rcases i with ⟨i, hi⟩
          interval_cases i <;>
            simp [PrimitiveAffineEightFrameRow0ModuleRepresentation.charts, displacementCharts])

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

end
