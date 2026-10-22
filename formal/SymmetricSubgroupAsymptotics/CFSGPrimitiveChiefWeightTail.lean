import SymmetricSubgroupAsymptotics.CFSGPrimitiveNonaffineChiefWeightTail
import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineChiefWeightTail
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof

/-! Primitive degree≥45 chief weights from original orders, with no
primitive composition-length or ordinary normal-generator premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open PrimitiveSocleRawStructure

theorem primitiveChiefThreeTenths_tail_of_sufficient
    (hindex : SufficientSimpleIndexBounds)
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (hf : 45 ≤ Nat.card X) (c : ActualChiefSeries G) :
    10*actualChiefSeriesTernaryWeight c ≤ 3*Nat.card X := by
  cases Classical.choice (publishedONanScottStructure G X) with
  | inl D =>
      have hh := D.chiefThreeWeight_strict_tail hindex (by omega) c
      omega
  | inr P => exact P.chiefThreeWeight_threeTenths_tail inferInstance hf c

end SymmetricSubgroupAsymptotics
