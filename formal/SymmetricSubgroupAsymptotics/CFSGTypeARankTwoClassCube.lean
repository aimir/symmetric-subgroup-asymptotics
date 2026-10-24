import SymmetricSubgroupAsymptotics.SLThreeConjugacyClassBound
import SymmetricSubgroupAsymptotics.CFSGTypeAOuterGcdCardinality
import SymmetricSubgroupAsymptotics.CFSGTypeAMinimumIndexLower
import SymmetricSubgroupAsymptotics.CFSGTypeALeastIndexSquare
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart
import SymmetricSubgroupAsymptotics.RankTwoClassCubeNumerics
import Mathlib.Data.Nat.Prime.Int

/-! Actual rank-two A class/outer capacity for all field orders at least
three. Every class bound descends along the original SL-to-PSL quotient;
proper-index and square budgets remain attached to that same model.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeARankTwoClassCube
open PrimitiveSocleRawStructure

theorem class_card_le (q:CFSG.PrimePower) :
    Nat.card (ConjClasses (CFSG.Models.A 2 q)) ≤
      (q.order-1).gcd 3*(q.order^2+2*q.order) := by
  letI : Finite (Matrix.SpecialLinearGroup (Fin 3) q.Field) :=
    Finite.of_injective (fun A:Matrix.SpecialLinearGroup (Fin 3) q.Field=>A.val)
      Subtype.val_injective
  let f : Matrix.SpecialLinearGroup (Fin 3) q.Field →* CFSG.Models.A 2 q :=
    QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) q.Field))
  have hc : Nat.card (ConjClasses (CFSG.Models.A 2 q)) ≤
      Nat.card (ConjClasses (Matrix.SpecialLinearGroup (Fin 3) q.Field)) :=
    Nat.card_le_card_of_surjective (ConjClasses.map f)
      (ConjClasses.map_surjective (QuotientGroup.mk'_surjective _))
  exact hc.trans (by simpa only [q.card_field] using SLThreeConjugacyClassBound.class_card_le q.Field)

theorem proper_index_lower (q:CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.A 2 q)]
    (K:Subgroup (CFSG.Models.A 2 q)) (hK:K≠⊤) : q.order^2≤K.index := by
  simpa only [q.card_field] using
    CFSGTypeAIndexReindex.field_power_le_proper_index (F:=q.Field) 2 (by decide) K hK

theorem field_fourth_le_card (q:CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.A 2 q)] :
    (q.order^2)^2≤Nat.card (CFSG.Models.A 2 q) := by
  obtain ⟨ell,hell⟩ := exists_leastProperIndex (CFSG.Models.A 2 q)
  have hi := CFSGTypeAMinimumIndexLower.order_power_le_leastProperIndex 2 (by decide) q ell hell
  have hs := CFSGTypeALeastIndexSquare.typeA_leastProperIndex_square_lt_card 2 (by decide) q ell hell
  exact (Nat.pow_le_pow_left hi 2).trans hs.le

theorem component_class_cube (q:CFSG.PrimePower) (hq:3≤q.order)
    [IsSimpleGroup (CFSG.Models.A 2 q)] :
    (Nat.card (ConjClasses (CFSG.Models.A 2 q))*Nat.card (Outer (CFSG.Models.A 2 q)))^3 ≤
      5^(q.order^2-1) := by
  have hc := class_card_le q
  have ho := CFSGTypeAOuterGcdCardinality.typeA_higher_outer_card_le_gcd 2 (by decide) q
  by_cases hfour:4≤q.order
  · exact (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3).trans
      (RankTwoClassCubeNumerics.cubic_budget_of_four_le q.order q.exponent
        ((q.order-1).gcd 3) hfour
        (RankTwoClassCubeNumerics.twice_exponent_le_prime_power q.prime q.exponent
          q.prime_isPrime.two_le q.exponent_pos)
        (Nat.gcd_le_right _ (by decide)))
  · have heq:q.order=3 := by omega
    have he:q.exponent=1 :=
      (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 3)
        q.exponent_pos.ne' (by decide : (1:ℕ)≠0)
        (show q.prime^q.exponent=3^1 from heq)).2
    have hc':Nat.card (ConjClasses (CFSG.Models.A 2 q))≤15 := by
      simpa only [heq] using hc
    have ho':Nat.card (Outer (CFSG.Models.A 2 q))≤2 := by
      simpa only [heq,he] using ho
    rw [heq]
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul hc' ho') 3).trans
      (by decide : (15*2)^3≤5^(3^2-1))

end SymmetricSubgroupAsymptotics.CFSGTypeARankTwoClassCube
