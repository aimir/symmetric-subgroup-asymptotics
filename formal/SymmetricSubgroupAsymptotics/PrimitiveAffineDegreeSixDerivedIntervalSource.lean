import SymmetricSubgroupAsymptotics.Non2PreE7DerivedTailIntervalSource
import SymmetricSubgroupAsymptotics.Non2PreE7SelfComparatorSource

/-!
# A degree-six interval closed by ternary derived targets

Axes containing a fixed normal ternary section are quotients of its faithful
four-point comparator.  On every remaining axis, one ternary cyclic-dual
target gives the common `3^(b/3)` tail.  This file supplies all uniform
constants and menu summations, leaving concrete affine cells only the
structural target construction.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private abbrev DegreeSixAxis (U : PreE7NonPairActionClass 6) :=
  {N : Subgroup (preE7NonPairAction 6 U) // N.Normal}

/-- Structural data for a degree-six ternary interval.  The derived depth
may depend on the literal normal axis; its counting exponent does not. -/
structure PreE7DegreeSixTernaryDerivedIntervalData
    (U : PreE7NonPairActionClass 6) : Type 1 where
  E : Subgroup (preE7NonPairAction 6 U)
  [E_normal : E.Normal]
  quotientAction :
    (preE7NonPairAction 6 U ⧸ E) →* Equiv.Perm (Fin 4)
  quotientAction_injective : Function.Injective quotientAction
  target : ∀ (N : DegreeSixAxis U), ¬ E ≤ N.1 →
    Σ n : ℕ, DerivedHead.DerivedCyclicTarget
      (preE7NonPairAction 6 U ⧸ N.1)
      (E.map (QuotientGroup.mk' N.1)) n 3

attribute [instance] PreE7DegreeSixTernaryDerivedIntervalData.E_normal

namespace PreE7DegreeSixTernaryDerivedIntervalData

variable {U : PreE7NonPairActionClass 6}
  (D : PreE7DegreeSixTernaryDerivedIntervalData U)

/-- Uniform tail on every quotient retaining the ternary section. -/
theorem quotient_tail
    (N : DegreeSixAxis U) (hN : ¬ D.E ≤ N.1)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J
      (preE7NonPairAction 6 U ⧸ N.1)) : ℝ) ≤
      (2 : ℝ) ^ (102 : ℕ) *
        (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
  let T := D.target N hN
  have htarget := T.2.epi_card_le_ternary J
  apply htarget.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have horder :=
    (degreeSix_subgroup_and_quotient_order_le
      (preE7NonPairAction 6 U) N.1).2
  have hAut : Nat.card
      ((preE7NonPairAction 6 U ⧸ N.1) ≃*
        (preE7NonPairAction 6 U ⧸ N.1)) ≤ 2 ^ 100 := by
    simpa using mulEquiv_card_le_two_pow_sq_of_order 10 horder
  have hAut' : Nat.card
      ((preE7NonPairAction 6 U ⧸ N.1) ≃*
        (preE7NonPairAction 6 U ⧸ N.1)) ≤ 2 ^ 102 :=
    hAut.trans (by norm_num)
  exact_mod_cast hAut'

/-- The comparator indicator has no larger total mass than the full literal
normal menu. -/
theorem main_total_bound (b : ℕ) :
    fusionAxisEnvelopeTotal (preE7NonPairAction 6 U)
        (fun N => if D.E ≤ N.1 then 1 else 0) ≤
      (2 : ℝ) ^
        (16 * (6 : ℝ) * Real.log ((6 + b + 2 : ℕ) : ℝ) ^ 2) := by
  calc
    fusionAxisEnvelopeTotal (preE7NonPairAction 6 U)
        (fun N => if D.E ≤ N.1 then 1 else 0) ≤
        fusionAxisEnvelopeTotal (preE7NonPairAction 6 U)
          (fun _ => (2 : ℝ) ^ (102 : ℕ)) := by
      unfold fusionAxisEnvelopeTotal
      exact Finset.sum_le_sum (fun N _ => by split <;> norm_num)
    _ ≤ (2 : ℝ) ^ (202 : ℕ) :=
      PrimitiveAffineDegreeSixTailSource.coefficient_total_le U
    _ = Real.rpow (2 : ℝ) (202 : ℝ) := by simp
    _ ≤ Real.rpow (2 : ℝ) (36 * (6 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      norm_num
    _ ≤ _ := two_rpow_thirtySix_width_le_menuMass
      (w := 6) (by norm_num) b

/-- The one uniform tail coefficient on every retained axis still fits the
degree-six logarithmic menu allowance. -/
theorem tail_total_bound (b : ℕ) :
    fusionAxisEnvelopeTotal (preE7NonPairAction 6 U)
        (fun N => if D.E ≤ N.1 then 0 else (2 : ℝ) ^ (102 : ℕ)) ≤
      (2 : ℝ) ^
        (16 * (6 : ℝ) * Real.log ((6 + b + 2 : ℕ) : ℝ) ^ 2) := by
  calc
    fusionAxisEnvelopeTotal (preE7NonPairAction 6 U)
        (fun N => if D.E ≤ N.1 then 0 else (2 : ℝ) ^ (102 : ℕ)) ≤
        fusionAxisEnvelopeTotal (preE7NonPairAction 6 U)
          (fun _ => (2 : ℝ) ^ (102 : ℕ)) := by
      unfold fusionAxisEnvelopeTotal
      apply Finset.sum_le_sum
      intro N _
      split <;> norm_num
    _ ≤ (2 : ℝ) ^ (202 : ℕ) :=
      PrimitiveAffineDegreeSixTailSource.coefficient_total_le U
    _ = Real.rpow (2 : ℝ) (202 : ℝ) := by simp
    _ ≤ Real.rpow (2 : ℝ) (36 * (6 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      norm_num
    _ ≤ _ := two_rpow_thirtySix_width_le_menuMass
      (w := 6) (by norm_num) b

/-- Install the complete small-additive interval. -/
noncomputable def intervalData :
    PreE7DerivedTailIntervalSourceData 6 U where
  E := D.E
  quotientDegree := 4
  quotientAction := D.quotientAction
  quotientAction_injective := D.quotientAction_injective
  theta := Real.logb 2 3 / 3
  comparator_window := by
    norm_num [preE7CharacterRho, evenWidth, halfDegree]
  tail_window := logThreeThird_le_window (by norm_num)
  tailCoefficient := fun _ => (2 : ℝ) ^ (102 : ℕ)
  tailCoefficient_nonneg := fun _ => by positivity
  tail_bound := D.quotient_tail
  main_total_bound := D.main_total_bound
  tail_total_bound := D.tail_total_bound

/-- Final ordinary rank-tail source. -/
noncomputable def source : PreE7RankTailSourceOrYonedaTopData 6 U :=
  D.intervalData.toRankTailSourceOrYonedaTop

end PreE7DegreeSixTernaryDerivedIntervalData
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
