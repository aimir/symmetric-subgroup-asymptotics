import SymmetricSubgroupAsymptotics.CFSGPrimitiveTernaryOrderBounds

/-! Every ORIGINAL actual chief series obeys the raw order bounds. No
comparison with an optimized/replacement chief series or composition
length is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open CFSGPrimitiveTernaryTailNumerics

namespace PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.chiefThreeWeight_le_logSquare
    (D : NonaffineData G X) (hindex : SufficientSimpleIndexBounds)
    (c : ActualChiefSeries G) : actualChiefSeriesTernaryWeight c ≤
      (Nat.log2 (Nat.card X)+1)^2+2*(Nat.log2 (Nat.card X)+1) := by
  refine (actualChiefSeriesTernaryWeight_le_semisimpleQuotient_factorization
    (finiteGroupSocle G) D.chart c).trans (Nat.factorization_le_of_le_pow ?_)
  exact (D.quotient_card_le_dyadic hindex).trans
    (Nat.pow_le_pow_left (by decide : 2 ≤ 3) _)

end PrimitiveSocleRawStructure

namespace PrimitiveAffineProfile
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X]

theorem chiefThreeWeight_le_logSquare (P : PrimitiveAffineProfile G X)
    (hp : MulAction.IsPreprimitive G X) (c : ActualChiefSeries G) :
    actualChiefSeriesTernaryWeight c ≤ (Nat.log2 (Nat.card X)+1)^2 := by
  refine (actualChiefSeriesTernaryWeight_le_order c).trans
    (Nat.factorization_le_of_le_pow ?_)
  exact (P.card_le_dyadic_logSquare hp).trans
    (Nat.pow_le_pow_left (by decide : 2 ≤ 3) _)

end PrimitiveAffineProfile
end SymmetricSubgroupAsymptotics
