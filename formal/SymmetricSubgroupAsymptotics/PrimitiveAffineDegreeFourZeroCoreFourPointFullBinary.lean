import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalFullBinarySocleCapacity
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourNonbinaryFourPointCharts
import SymmetricSubgroupAsymptotics.ElementaryNormalModuleGenerators

/-! Dispatch the actual zero-core four-block top to its internally
constructed A4/S4 chart. The bound concerns the full binary socle of each
original quotient, including its central trivial constituents. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

local instance primitiveAffineDegreeFourZeroCoreFourPointFullBinary_localFact1 : Fact P.p.Prime := ⟨P.p_prime⟩

local instance zeroCoreFourPointFullBinary_scalarModule
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Module (ZMod P.p) (DegreeFourFullBinarySocleChart block P N).V :=
  (DegreeFourFullBinarySocleChart block P N).module

theorem degreeFourZeroCore_fourPoint_fullBinary_generated
    (hr : Nat.card block.Fibre = 4) (hs : Nat.card block.Points = 4)
    (hD : degreeFourTernaryCore block P = ⊥) (hTop : ¬ IsPGroup 2 block.Top)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    RepresentationGeneratedBy (degreeFourOriginalBinarySocleInflated block P N) 2 := by
  rcases degreeFour_nonbinary_actual_pointCharts block hs hTop with hA | hS
  · rcases hA with ⟨C⟩
    exact DegreeFourA4OriginalPointChart.originalFullBinarySocle_generated_le_two
      (block := block) (P := P) (C := C) hr hD N
  · rcases hS with ⟨C⟩
    exact DegreeFourS4OriginalPointChart.originalFullBinarySocle_generated_le_two
      (block := block) (P := P) (C := C) hr hD N

theorem degreeFourZeroCore_fourPoint_fullBinary_normalGen_le_two
    (hr : Nat.card block.Fibre = 4) (hs : Nat.card block.Points = 4)
    (hD : degreeFourTernaryCore block P = ⊥) (hTop : ¬ IsPGroup 2 block.Top)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    MarkedC4.normalGen (DegreeFourFullBinarySocle block P N) ≤ 2 := by
  let A := DegreeFourFullBinarySocle block P N
  let C := DegreeFourFullBinarySocleChart block P N
  letI : Module (ZMod P.p) C.V := C.module
  let sigma : Representation (ZMod P.p) _ C.V := C.quotientRepresentation.ρ
  let t := degreeFourFullBinarySocleTopMap block P N
  have hg : RepresentationGeneratedBy (sigma.comp t) 2 :=
    degreeFourZeroCore_fourPoint_fullBinary_generated block P hr hs hD hTop N
  exact normalGen_le_of_elementaryQuotientRepresentation_generated A C 2
    (RepresentationGeneratedBy.of_comp sigma t hg)

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
