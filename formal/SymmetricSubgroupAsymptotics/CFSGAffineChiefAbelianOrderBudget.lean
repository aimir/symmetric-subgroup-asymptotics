import SymmetricSubgroupAsymptotics.CFSGChiefPrimeFactorBudget
import SymmetricSubgroupAsymptotics.CFSGPrimitiveTernaryOrderBounds
import SymmetricSubgroupAsymptotics.MarkedC4AbelianSectionSize

/-! Elementary order bounds for every actual affine chief series. These
are weaker than a primitive composition-length theorem and suffice for
the large-component capacity consumer. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem cardFactors_le_dyadic_exponent {n a : ℕ} (hn : n ≠ 0) (ha : n ≤ 2^a) :
    ArithmeticFunction.cardFactors n ≤ a := by
  have hh : 2^(ArithmeticFunction.cardFactors n) ≤ n := by
    simpa only [ArithmeticFunction.cardFactors_apply, MarkedC4.AbelianSectionSize.omega] using
      (MarkedC4.AbelianSectionSize.two_pow_omega_le hn)
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hh.trans ha)

namespace PrimitiveAffineProfile
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X]

theorem chiefAbelianLength_le_logSquare (P : PrimitiveAffineProfile G X)
    (hp : MulAction.IsPreprimitive G X) (c : ActualChiefSeries G) :
    actualChiefSeriesAbelianLength c ≤ (Nat.log2 (Nat.card X)+1)^2 := by
  exact (actualChiefSeriesAbelianLength_le_cardFactors c).trans
    (cardFactors_le_dyadic_exponent Nat.card_pos.ne' (P.card_le_dyadic_logSquare hp))

theorem chiefAbelianLength_le_fullAffineOmega (P : PrimitiveAffineProfile G X)
    (hp : MulAction.IsPreprimitive G X) (c : ActualChiefSeries G)
    {p d : ℕ} (hp' : p.Prime) (hd : 0 < d) (hdegree : Nat.card X = p^d) :
    actualChiefSeriesAbelianLength c ≤ ArithmeticFunction.cardFactors (fullAffineOrder p d) := by
  obtain ⟨q,e,hq,he,heq,hdiv,hne⟩ := P.exists_prime_dimension_order_divisor hp
  obtain ⟨rfl,rfl⟩ := prime_pow_positive_injective hq hp' he hd (heq.symm.trans hdegree)
  exact (actualChiefSeriesAbelianLength_le_cardFactors c).trans
    (CFSGChiefPrimeFactorBudget.cardFactors_mono hne hdiv)

end PrimitiveAffineProfile
end SymmetricSubgroupAsymptotics
