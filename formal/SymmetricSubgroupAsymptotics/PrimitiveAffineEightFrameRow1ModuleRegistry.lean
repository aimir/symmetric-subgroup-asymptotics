import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoins
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryDisplacement0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryDisplacement8
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryDisplacement16
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryDisplacement24
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryDisplacement32
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryDisplacement40
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryDisplacement48
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryDisplacement56
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryDisplacement64
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryDisplacement72
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryDisplacement80
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryDisplacement88
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryDisplacement96
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryDisplacement104
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryDisplacement112
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryDisplacement120
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryDisplacement128
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryDisplacement136

/-! Assembly of the checked cyclic joins and displacement chunks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

local instance sourceGroupAssembly : Group Source := PrimitiveAffineEightFrameRow1TopCertificate.group
local instance sourceInhabitedAssembly : Inhabited Source := ⟨1⟩

noncomputable def displacementCharts (i : Fin 143) :
    Σ d, BinaryCoordinateSpace 16 d :=
  (if i.val < 71 then (if i.val < 35 then (if i.val < 17 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ⟨0, D0.displacementChart⟩ else ⟨2, D1.displacementChart⟩) else (if i.val < 3 then ⟨2, D2.displacementChart⟩ else ⟨2, D3.displacementChart⟩)) else (if i.val < 6 then (if i.val < 5 then ⟨2, D4.displacementChart⟩ else ⟨2, D5.displacementChart⟩) else (if i.val < 7 then ⟨2, D6.displacementChart⟩ else ⟨4, D7.displacementChart⟩))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then ⟨3, D8.displacementChart⟩ else ⟨3, D9.displacementChart⟩) else (if i.val < 11 then ⟨3, D10.displacementChart⟩ else ⟨4, D11.displacementChart⟩)) else (if i.val < 14 then (if i.val < 13 then ⟨4, D12.displacementChart⟩ else ⟨4, D13.displacementChart⟩) else (if i.val < 15 then ⟨4, D14.displacementChart⟩ else (if i.val < 16 then ⟨4, D15.displacementChart⟩ else ⟨4, D16.displacementChart⟩))))) else (if i.val < 26 then (if i.val < 21 then (if i.val < 19 then (if i.val < 18 then ⟨4, D17.displacementChart⟩ else ⟨4, D18.displacementChart⟩) else (if i.val < 20 then ⟨4, D19.displacementChart⟩ else ⟨4, D20.displacementChart⟩)) else (if i.val < 23 then (if i.val < 22 then ⟨4, D21.displacementChart⟩ else ⟨4, D22.displacementChart⟩) else (if i.val < 24 then ⟨4, D23.displacementChart⟩ else (if i.val < 25 then ⟨4, D24.displacementChart⟩ else ⟨4, D25.displacementChart⟩)))) else (if i.val < 30 then (if i.val < 28 then (if i.val < 27 then ⟨5, D26.displacementChart⟩ else ⟨5, D27.displacementChart⟩) else (if i.val < 29 then ⟨5, D28.displacementChart⟩ else ⟨4, D29.displacementChart⟩)) else (if i.val < 32 then (if i.val < 31 then ⟨5, D30.displacementChart⟩ else ⟨5, D31.displacementChart⟩) else (if i.val < 33 then ⟨5, D32.displacementChart⟩ else (if i.val < 34 then ⟨6, D33.displacementChart⟩ else ⟨6, D34.displacementChart⟩)))))) else (if i.val < 53 then (if i.val < 44 then (if i.val < 39 then (if i.val < 37 then (if i.val < 36 then ⟨6, D35.displacementChart⟩ else ⟨5, D36.displacementChart⟩) else (if i.val < 38 then ⟨5, D37.displacementChart⟩ else ⟨5, D38.displacementChart⟩)) else (if i.val < 41 then (if i.val < 40 then ⟨5, D39.displacementChart⟩ else ⟨5, D40.displacementChart⟩) else (if i.val < 42 then ⟨5, D41.displacementChart⟩ else (if i.val < 43 then ⟨5, D42.displacementChart⟩ else ⟨5, D43.displacementChart⟩)))) else (if i.val < 48 then (if i.val < 46 then (if i.val < 45 then ⟨5, D44.displacementChart⟩ else ⟨6, D45.displacementChart⟩) else (if i.val < 47 then ⟨6, D46.displacementChart⟩ else ⟨6, D47.displacementChart⟩)) else (if i.val < 50 then (if i.val < 49 then ⟨6, D48.displacementChart⟩ else ⟨6, D49.displacementChart⟩) else (if i.val < 51 then ⟨6, D50.displacementChart⟩ else (if i.val < 52 then ⟨6, D51.displacementChart⟩ else ⟨6, D52.displacementChart⟩))))) else (if i.val < 62 then (if i.val < 57 then (if i.val < 55 then (if i.val < 54 then ⟨6, D53.displacementChart⟩ else ⟨6, D54.displacementChart⟩) else (if i.val < 56 then ⟨7, D55.displacementChart⟩ else ⟨7, D56.displacementChart⟩)) else (if i.val < 59 then (if i.val < 58 then ⟨7, D57.displacementChart⟩ else ⟨8, D58.displacementChart⟩) else (if i.val < 60 then ⟨7, D59.displacementChart⟩ else (if i.val < 61 then ⟨7, D60.displacementChart⟩ else ⟨7, D61.displacementChart⟩)))) else (if i.val < 66 then (if i.val < 64 then (if i.val < 63 then ⟨7, D62.displacementChart⟩ else ⟨7, D63.displacementChart⟩) else (if i.val < 65 then ⟨7, D64.displacementChart⟩ else ⟨7, D65.displacementChart⟩)) else (if i.val < 68 then (if i.val < 67 then ⟨6, D66.displacementChart⟩ else ⟨7, D67.displacementChart⟩) else (if i.val < 69 then ⟨7, D68.displacementChart⟩ else (if i.val < 70 then ⟨7, D69.displacementChart⟩ else ⟨7, D70.displacementChart⟩))))))) else (if i.val < 107 then (if i.val < 89 then (if i.val < 80 then (if i.val < 75 then (if i.val < 73 then (if i.val < 72 then ⟨6, D71.displacementChart⟩ else ⟨7, D72.displacementChart⟩) else (if i.val < 74 then ⟨7, D73.displacementChart⟩ else ⟨7, D74.displacementChart⟩)) else (if i.val < 77 then (if i.val < 76 then ⟨7, D75.displacementChart⟩ else ⟨6, D76.displacementChart⟩) else (if i.val < 78 then ⟨8, D77.displacementChart⟩ else (if i.val < 79 then ⟨8, D78.displacementChart⟩ else ⟨8, D79.displacementChart⟩)))) else (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then ⟨8, D80.displacementChart⟩ else ⟨8, D81.displacementChart⟩) else (if i.val < 83 then ⟨8, D82.displacementChart⟩ else ⟨8, D83.displacementChart⟩)) else (if i.val < 86 then (if i.val < 85 then ⟨8, D84.displacementChart⟩ else ⟨8, D85.displacementChart⟩) else (if i.val < 87 then ⟨8, D86.displacementChart⟩ else (if i.val < 88 then ⟨8, D87.displacementChart⟩ else ⟨8, D88.displacementChart⟩))))) else (if i.val < 98 then (if i.val < 93 then (if i.val < 91 then (if i.val < 90 then ⟨7, D89.displacementChart⟩ else ⟨7, D90.displacementChart⟩) else (if i.val < 92 then ⟨7, D91.displacementChart⟩ else ⟨8, D92.displacementChart⟩)) else (if i.val < 95 then (if i.val < 94 then ⟨8, D93.displacementChart⟩ else ⟨8, D94.displacementChart⟩) else (if i.val < 96 then ⟨7, D95.displacementChart⟩ else (if i.val < 97 then ⟨7, D96.displacementChart⟩ else ⟨7, D97.displacementChart⟩)))) else (if i.val < 102 then (if i.val < 100 then (if i.val < 99 then ⟨7, D98.displacementChart⟩ else ⟨7, D99.displacementChart⟩) else (if i.val < 101 then ⟨7, D100.displacementChart⟩ else ⟨9, D101.displacementChart⟩)) else (if i.val < 104 then (if i.val < 103 then ⟨9, D102.displacementChart⟩ else ⟨9, D103.displacementChart⟩) else (if i.val < 105 then ⟨8, D104.displacementChart⟩ else (if i.val < 106 then ⟨8, D105.displacementChart⟩ else ⟨8, D106.displacementChart⟩)))))) else (if i.val < 125 then (if i.val < 116 then (if i.val < 111 then (if i.val < 109 then (if i.val < 108 then ⟨8, D107.displacementChart⟩ else ⟨9, D108.displacementChart⟩) else (if i.val < 110 then ⟨9, D109.displacementChart⟩ else ⟨9, D110.displacementChart⟩)) else (if i.val < 113 then (if i.val < 112 then ⟨10, D111.displacementChart⟩ else ⟨10, D112.displacementChart⟩) else (if i.val < 114 then ⟨10, D113.displacementChart⟩ else (if i.val < 115 then ⟨10, D114.displacementChart⟩ else ⟨10, D115.displacementChart⟩)))) else (if i.val < 120 then (if i.val < 118 then (if i.val < 117 then ⟨10, D116.displacementChart⟩ else ⟨9, D117.displacementChart⟩) else (if i.val < 119 then ⟨9, D118.displacementChart⟩ else ⟨9, D119.displacementChart⟩)) else (if i.val < 122 then (if i.val < 121 then ⟨10, D120.displacementChart⟩ else ⟨10, D121.displacementChart⟩) else (if i.val < 123 then ⟨10, D122.displacementChart⟩ else (if i.val < 124 then ⟨10, D123.displacementChart⟩ else ⟨10, D124.displacementChart⟩))))) else (if i.val < 134 then (if i.val < 129 then (if i.val < 127 then (if i.val < 126 then ⟨10, D125.displacementChart⟩ else ⟨10, D126.displacementChart⟩) else (if i.val < 128 then ⟨11, D127.displacementChart⟩ else ⟨11, D128.displacementChart⟩)) else (if i.val < 131 then (if i.val < 130 then ⟨11, D129.displacementChart⟩ else ⟨11, D130.displacementChart⟩) else (if i.val < 132 then ⟨11, D131.displacementChart⟩ else (if i.val < 133 then ⟨11, D132.displacementChart⟩ else ⟨12, D133.displacementChart⟩)))) else (if i.val < 138 then (if i.val < 136 then (if i.val < 135 then ⟨12, D134.displacementChart⟩ else ⟨12, D135.displacementChart⟩) else (if i.val < 137 then ⟨12, D136.displacementChart⟩ else ⟨12, D137.displacementChart⟩)) else (if i.val < 140 then (if i.val < 139 then ⟨12, D138.displacementChart⟩ else ⟨13, D139.displacementChart⟩) else (if i.val < 141 then ⟨13, D140.displacementChart⟩ else (if i.val < 142 then ⟨13, D141.displacementChart⟩ else ⟨16, D142.displacementChart⟩))))))))

noncomputable def displacementCertificate (i : Fin 143) :
    BinaryCoordinateDisplacementCertificate
      PrimitiveAffineEightFrameRow1ModuleRepresentation.representation PrimitiveAffineEightFrameRow1TopCertificate.ambient
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states i) (displacementCharts i).2 := by
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
  · exact D101.certificate
  · exact D102.certificate
  · exact D103.certificate
  · exact D104.certificate
  · exact D105.certificate
  · exact D106.certificate
  · exact D107.certificate
  · exact D108.certificate
  · exact D109.certificate
  · exact D110.certificate
  · exact D111.certificate
  · exact D112.certificate
  · exact D113.certificate
  · exact D114.certificate
  · exact D115.certificate
  · exact D116.certificate
  · exact D117.certificate
  · exact D118.certificate
  · exact D119.certificate
  · exact D120.certificate
  · exact D121.certificate
  · exact D122.certificate
  · exact D123.certificate
  · exact D124.certificate
  · exact D125.certificate
  · exact D126.certificate
  · exact D127.certificate
  · exact D128.certificate
  · exact D129.certificate
  · exact D130.certificate
  · exact D131.certificate
  · exact D132.certificate
  · exact D133.certificate
  · exact D134.certificate
  · exact D135.certificate
  · exact D136.certificate
  · exact D137.certificate
  · exact D138.certificate
  · exact D139.certificate
  · exact D140.certificate
  · exact D141.certificate
  · exact D142.certificate

/-- Literal displacement spaces have codimension at most two in every
invariant state, while the cyclic join table is complete. -/
noncomputable def registry :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry PrimitiveAffineEightFrameRow1ModuleRepresentation.representation 2 :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry.ofBinaryCoordinateCertificates
        PrimitiveAffineEightFrameRow1ModuleRepresentation.states axes PrimitiveAffineEightFrameRow1TopCertificate.ambient
        (fun i ↦ (displacementCharts i).1)
        (fun i ↦ (displacementCharts i).2)
        displacementCertificate (by
          intro i
          rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space,
            (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts i).2.finrank]
          change (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts i).1 ≤
            (displacementCharts i).1 + 2
          rcases i with ⟨i, hi⟩
          interval_cases i <;>
            simp [PrimitiveAffineEightFrameRow1ModuleRepresentation.charts, displacementCharts])

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

end
