import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallPrimeBudgets

/-!
# Literal small-prime sources for small affine components

This file applies the checked small-prime budgets to the actual primitive
component and the actual number of blocks.  No abstract overgroup replaces
the component: its order enters through the exact divisors `20`, `1344`,
`432`, and `322560`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace ComponentSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
  (hTraceyLog : TraceyAffineInducedModuleInput)
  (hTraceyRefined : TraceyRefinedInducedModuleInput)
  (hTraceyPerm : TraceyPermutationGeneratorInput)
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

private abbrev blocks := Nat.card block.Points

private noncomputable def degreeFive_of_budget
    (hr : Nat.card block.Fibre = 5)
    (q e : ℕ) (hq : q.Prime) (he : 1 ≤ e)
    (hqdiv : q ^ e ∣ blocks block)
    (hqmax : ¬ q ^ (e + 1) ∣ blocks block)
    (k : ℝ)
    (hbudget : refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate (blocks block) q e) 20 ≤
      k * blocks block)
    (hnum : preE7CharacterRho * (5 : ℝ) + k + 1 / 16 ≤ (5 - 1 : ℝ) / 8) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P q e 20 hq he hqdiv hqmax (by norm_num)
  · have hprime : (Nat.card block.Fibre).Prime := by rw [hr]; norm_num
    have h := component_card_dvd_prime_mul_pred block P hprime
    simpa only [hr] using h
  · exact smallAffine_budget_margin 5 (blocks block) w block.degrees_ge_two.2
      (by simpa only [hr] using width_eq block) k _ hnum hbudget

private noncomputable def degreeEight_of_budget
    (hr : Nat.card block.Fibre = 8)
    (q e : ℕ) (hq : q.Prime) (he : 1 ≤ e)
    (hqdiv : q ^ e ∣ blocks block)
    (hqmax : ¬ q ^ (e + 1) ∣ blocks block)
    (k : ℝ)
    (hbudget : refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate (blocks block) q e) 1344 ≤
      k * blocks block)
    (hnum : preE7CharacterRho * (8 : ℝ) + k + 1 / 16 ≤ (8 - 1 : ℝ) / 8) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P q e 1344 hq he hqdiv hqmax (by norm_num)
  · exact component_card_dvd_1344 block P hr
  · exact smallAffine_budget_margin 8 (blocks block) w block.degrees_ge_two.2
      (by simpa only [hr] using width_eq block) k _ hnum hbudget

private noncomputable def degreeNine_of_budget
    (hr : Nat.card block.Fibre = 9)
    (q e : ℕ) (hq : q.Prime) (he : 1 ≤ e)
    (hqdiv : q ^ e ∣ blocks block)
    (hqmax : ¬ q ^ (e + 1) ∣ blocks block)
    (k : ℝ)
    (hbudget : refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate (blocks block) q e) 432 ≤
      k * blocks block)
    (hnum : preE7CharacterRho * (9 : ℝ) + k + 1 / 16 ≤ (9 - 1 : ℝ) / 8) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P q e 432 hq he hqdiv hqmax (by norm_num)
  · exact component_card_dvd_432 block P hr
  · exact smallAffine_budget_margin 9 (blocks block) w block.degrees_ge_two.2
      (by simpa only [hr] using width_eq block) k _ hnum hbudget

private noncomputable def degreeSixteen_of_budget
    (hr : Nat.card block.Fibre = 16)
    (q e : ℕ) (hq : q.Prime) (he : 1 ≤ e)
    (hqdiv : q ^ e ∣ blocks block)
    (hqmax : ¬ q ^ (e + 1) ∣ blocks block)
    (k : ℝ)
    (hbudget : refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate (blocks block) q e) 322560 ≤
      k * blocks block)
    (hnum : preE7CharacterRho * (16 : ℝ) + k + 1 / 16 ≤ (16 - 1 : ℝ) / 8) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P q e 322560 hq he hqdiv hqmax (by norm_num)
  · exact component_card_dvd_322560 block P hr
  · exact smallAffine_budget_margin 16 (blocks block) w block.degrees_ge_two.2
      (by simpa only [hr] using width_eq block) k _ hnum hbudget

/-! ## Prime five -/

noncomputable def of_degreeFive_primeFive
    (hr : Nat.card block.Fibre = 5) (e : ℕ) (he : 1 ≤ e)
    (hdiv : 5 ^ e ∣ blocks block) (hmax : ¬ 5 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeFive_of_budget hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    hr 5 e (by norm_num) he hdiv hmax (71 / 180)
      (refinedBudget_twenty_traceyPrimary_five (blocks block) e he) (by
        unfold preE7CharacterRho
        norm_num)

noncomputable def of_degreeEight_primeFive
    (hr : Nat.card block.Fibre = 8) (e : ℕ) (he : 1 ≤ e)
    (hdiv : 5 ^ e ∣ blocks block) (hmax : ¬ 5 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeEight_of_budget hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    hr 5 e (by norm_num) he hdiv hmax (887 / 1120)
      (refinedBudget_thirteenFortyFour_traceyPrimary_five (blocks block) e he) (by
        unfold preE7CharacterRho
        norm_num)

noncomputable def of_degreeNine_primeFive
    (hr : Nat.card block.Fibre = 9) (e : ℕ) (he : 1 ≤ e)
    (hdiv : 5 ^ e ∣ blocks block) (hmax : ¬ 5 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeNine_of_budget hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    hr 5 e (by norm_num) he hdiv hmax (23 / 32)
      (refinedBudget_fourThirtyTwo_traceyPrimary_five (blocks block) e he) (by
        unfold preE7CharacterRho
        norm_num)

noncomputable def of_degreeSixteen_primeFive
    (hr : Nat.card block.Fibre = 16) (e : ℕ) (he : 1 ≤ e)
    (hdiv : 5 ^ e ∣ blocks block) (hmax : ¬ 5 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeSixteen_of_budget hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    hr 5 e (by norm_num) he hdiv hmax (7523 / 5040)
      (refinedBudget_threeTwentyTwoFiveSixty_traceyPrimary_five
        (blocks block) e he) (by
          unfold preE7CharacterRho
          norm_num)

/-! ## Prime seven -/

noncomputable def of_degreeFive_primeSeven
    (hr : Nat.card block.Fibre = 5) (e : ℕ) (he : 1 ≤ e)
    (hdiv : 7 ^ e ∣ blocks block) (hmax : ¬ 7 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeFive_of_budget hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    hr 7 e (by norm_num) he hdiv hmax (22 / 105)
      (refinedBudget_twenty_traceyPrimary_seven (blocks block) e he) (by
        unfold preE7CharacterRho
        norm_num)

noncomputable def of_degreeEight_primeSeven
    (hr : Nat.card block.Fibre = 8) (e : ℕ) (he : 1 ≤ e)
    (hdiv : 7 ^ e ∣ blocks block) (hmax : ¬ 7 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeEight_of_budget hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    hr 7 e (by norm_num) he hdiv hmax (145 / 224)
      (refinedBudget_thirteenFortyFour_traceyPrimary_seven (blocks block) e he) (by
        unfold preE7CharacterRho
        norm_num)

noncomputable def of_degreeNine_primeSeven
    (hr : Nat.card block.Fibre = 9) (e : ℕ) (he : 1 ≤ e)
    (hdiv : 7 ^ e ∣ blocks block) (hmax : ¬ 7 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeNine_of_budget hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    hr 7 e (by norm_num) he hdiv hmax (115 / 224)
      (refinedBudget_fourThirtyTwo_traceyPrimary_seven (blocks block) e he) (by
        unfold preE7CharacterRho
        norm_num)

noncomputable def of_degreeSixteen_primeSeven
    (hr : Nat.card block.Fibre = 16) (e : ℕ) (he : 1 ≤ e)
    (hdiv : 7 ^ e ∣ blocks block) (hmax : ¬ 7 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeSixteen_of_budget hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    hr 7 e (by norm_num) he hdiv hmax (1807 / 1680)
      (refinedBudget_threeTwentyTwoFiveSixty_traceyPrimary_seven
        (blocks block) e he) (by
          unfold preE7CharacterRho
          norm_num)

/-! ## Prime three, exponent at least two -/

noncomputable def of_degreeFive_primeThree
    (hr : Nat.card block.Fibre = 5) (e : ℕ) (he : 2 ≤ e)
    (hdiv : 3 ^ e ∣ blocks block) (hmax : ¬ 3 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeFive_of_budget hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    hr 3 e (by norm_num) (by omega) hdiv hmax (22 / 135)
      (refinedBudget_twenty_traceyPrimary_three (blocks block) e he) (by
        unfold preE7CharacterRho
        norm_num)

noncomputable def of_degreeEight_primeThree
    (hr : Nat.card block.Fibre = 8) (e : ℕ) (he : 2 ≤ e)
    (hdiv : 3 ^ e ∣ blocks block) (hmax : ¬ 3 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeEight_of_budget hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    hr 3 e (by norm_num) (by omega) hdiv hmax (1619 / 2688)
      (refinedBudget_thirteenFortyFour_traceyPrimary_three (blocks block) e he) (by
        unfold preE7CharacterRho
        norm_num)

noncomputable def of_degreeNine_primeThree
    (hr : Nat.card block.Fibre = 9) (e : ℕ) (he : 2 ≤ e)
    (hdiv : 3 ^ e ∣ blocks block) (hmax : ¬ 3 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeNine_of_budget hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    hr 3 e (by norm_num) (by omega) hdiv hmax (1021 / 1152)
      (refinedBudget_fourThirtyTwo_traceyPrimary_three (blocks block) e he) (by
        unfold preE7CharacterRho
        norm_num)

noncomputable def of_degreeSixteen_primeThree
    (hr : Nat.card block.Fibre = 16) (e : ℕ) (he : 2 ≤ e)
    (hdiv : 3 ^ e ∣ blocks block) (hmax : ¬ 3 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeSixteen_of_budget hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    hr 3 e (by norm_num) (by omega) hdiv hmax (66391 / 60480)
      (refinedBudget_threeTwentyTwoFiveSixty_traceyPrimary_three
        (blocks block) e he) (by
          unfold preE7CharacterRho
          norm_num)

/-! ## Binary powers closed by the full component-order budget -/

noncomputable def of_degreeFive_primeTwo
    (hr : Nat.card block.Fibre = 5) (e : ℕ) (he : 5 ≤ e)
    (hdiv : 2 ^ e ∣ blocks block) (hmax : ¬ 2 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeFive_of_budget hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    hr 2 e (by norm_num) (by omega) hdiv hmax (187 / 480)
      (refinedBudget_twenty_traceyPrimary_two (blocks block) e he) (by
        unfold preE7CharacterRho
        norm_num)

noncomputable def of_degreeNine_primeTwo
    (hr : Nat.card block.Fibre = 9) (e : ℕ) (he : 4 ≤ e)
    (hdiv : 2 ^ e ∣ blocks block) (hmax : ¬ 2 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeNine_of_budget hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    hr 2 e (by norm_num) (by omega) hdiv hmax (1433 / 1536)
      (refinedBudget_fourThirtyTwo_traceyPrimary_two (blocks block) e he) (by
        unfold preE7CharacterRho
        norm_num)

end ComponentSource
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
