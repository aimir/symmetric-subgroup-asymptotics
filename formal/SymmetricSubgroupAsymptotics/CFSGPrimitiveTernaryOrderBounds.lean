import SymmetricSubgroupAsymptotics.CFSGPrimitiveTernaryTailNumerics
import SymmetricSubgroupAsymptotics.CFSGSufficientPrimitiveSocleQuotient
import SymmetricSubgroupAsymptotics.CFSGNonaffineCoarseComposition
import SymmetricSubgroupAsymptotics.OriginalNormalChiefHead
import SymmetricSubgroupAsymptotics.SemisimpleChiefWeightQuotientBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineLinearOrderDivisor
import SymmetricSubgroupAsymptotics.PrimitiveAffineHeadOrderBudget

/-! Actual original-order bounds for the primitive relative-three-head.
Nonaffine heads are charged only to the actual full-socle quotient. Affine
bounds use the literal translation dimension and faithful linear divisor. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
open CFSGPrimitiveTernaryTailNumerics

namespace PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.relativeThreeHead_le_quotient_valuation
    (D : NonaffineData G X) (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
      (Nat.card (G ⧸ finiteGroupSocle G)).factorization 3 := by
  exact (primeRelativeHead_le_actualChiefWeight N (actualChiefSeries G)).trans
    (actualChiefSeriesTernaryWeight_le_semisimpleQuotient_factorization
      (finiteGroupSocle G) D.chart (actualChiefSeries G))

theorem NonaffineData.quotient_card_le_dyadic
    (D : NonaffineData G X) (hindex : SufficientSimpleIndexBounds) :
    Nat.card (G ⧸ finiteGroupSocle G) ≤
      2^((Nat.log2 (Nat.card X)+1)^2 + 2*(Nat.log2 (Nat.card X)+1)) := by
  obtain ⟨ell, _, hf, hd, hb⟩ := D.sufficient_degree_lower hindex
  have ho : Nat.card (Outer D.Simple) ≤ ell^2 := by
    have hh := hb.square_bound hf
    omega
  exact (CFSGNonaffineCoarseComposition.quotient_card_le_outer_wreath D).trans
    (outer_wreath_order_dyadic (by omega) hd ho)

theorem NonaffineData.relativeThreeHead_le_logSquare
    (D : NonaffineData G X) (hindex : SufficientSimpleIndexBounds)
    (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
      (Nat.log2 (Nat.card X)+1)^2 + 2*(Nat.log2 (Nat.card X)+1) := by
  refine (D.relativeThreeHead_le_quotient_valuation N).trans
    (Nat.factorization_le_of_le_pow ?_)
  exact (D.quotient_card_le_dyadic hindex).trans (Nat.pow_le_pow_left (by decide : 2 ≤ 3) _)

end PrimitiveSocleRawStructure

theorem fullAffineOrder_le_degree_pow (p d : ℕ) :
    fullAffineOrder p d ≤ (p^d)^(d+1) := by
  have hl : fullLinearOrder p d ≤ (p^d)^d := by
    unfold fullLinearOrder
    calc
      (∏ i : Fin d, (p^d-p^i.val)) ≤ ∏ _i : Fin d, p^d :=
        Finset.prod_le_prod' (fun i _ => Nat.sub_le _ _)
      _ = (p^d)^d := by simp
  unfold fullAffineOrder
  calc
    p^d*fullLinearOrder p d ≤ p^d*(p^d)^d := Nat.mul_le_mul_left _ hl
    _ = (p^d)^(d+1) := by rw [pow_succ, Nat.mul_comm]

namespace PrimitiveAffineProfile
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X]

theorem card_le_dyadic_logSquare (P : PrimitiveAffineProfile G X)
    (hp : MulAction.IsPreprimitive G X) :
    Nat.card G ≤ 2^((Nat.log2 (Nat.card X)+1)^2) := by
  obtain ⟨p,d,hp',_,he,hdiv,hne⟩ := P.exists_prime_dimension_order_divisor hp
  have hx0 : Nat.card X ≠ 0 := by rw [he]; exact pow_ne_zero _ hp'.ne_zero
  have hd : d ≤ Nat.log2 (Nat.card X) := by
    rw [Nat.log2_eq_log_two]
    apply (Nat.le_log_iff_pow_le (by decide : 1 < 2) hx0).2
    rw [he]
    exact Nat.pow_le_pow_left hp'.two_le d
  have hu := log2_degree_upper hx0
  calc
    Nat.card G ≤ fullAffineOrder p d := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdiv
    _ ≤ (p^d)^(d+1) := fullAffineOrder_le_degree_pow p d
    _ = Nat.card X^(d+1) := by rw [he]
    _ ≤ (2^(Nat.log2 (Nat.card X)+1))^(d+1) := Nat.pow_le_pow_left hu _
    _ ≤ (2^(Nat.log2 (Nat.card X)+1))^(Nat.log2 (Nat.card X)+1) :=
      pow_le_pow_right₀ (one_le_pow₀ (by decide : 1 ≤ (2 : ℕ))) (by omega)
    _ = 2^((Nat.log2 (Nat.card X)+1)^2) := by rw [← pow_mul, pow_two]

theorem relativeThreeHead_le_logSquare (P : PrimitiveAffineProfile G X)
    (hp : MulAction.IsPreprimitive G X) (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
      (Nat.log2 (Nat.card X)+1)^2 := by
  refine (primeRelativeHead_le_groupFactorization 3 N).trans
    (Nat.factorization_le_of_le_pow ?_)
  exact (P.card_le_dyadic_logSquare hp).trans (Nat.pow_le_pow_left (by decide : 2 ≤ 3) _)

end PrimitiveAffineProfile
end SymmetricSubgroupAsymptotics
