import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallNumerics

/-!
# Small affine components at a large block-count prime

If the actual number of blocks has a prime divisor at least eleven, all
prime coordinates occurring in the four small affine component orders use
Tracey's prime-to rate.  The numerical margin proved in
`PrimitiveAffineImprimitiveSmallNumerics` therefore constructs the literal
component source directly.
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

/-- Local degree five, with a prime divisor at least eleven in the actual
block count. -/
noncomputable def of_degreeFive_largePrime
    (hr : Nat.card block.Fibre = 5)
    (q e : ℕ) (hq : q.Prime) (hq11 : 11 ≤ q) (he : 1 ≤ e)
    (hqdiv : q ^ e ∣ blocks block)
    (hqmax : ¬ q ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P q e 20 hq he hqdiv hqmax (by norm_num)
  · have hprime : (Nat.card block.Fibre).Prime := by rw [hr]; norm_num
    have h := component_card_dvd_prime_mul_pred block P hprime
    simpa only [hr] using h
  · apply smallAffine_largePrime_margin 5 (blocks block) w
      block.degrees_ge_two.2 (by simpa only [hr] using width_eq block)
      (22 / 15) _ (Or.inl ⟨rfl, rfl⟩)
    exact refinedBudget_twenty_traceyPrimary_largePrime
      (blocks block) q e hq hq11 he

/-- Local degree eight, with a prime divisor at least eleven in the actual
block count. -/
noncomputable def of_degreeEight_largePrime
    (hr : Nat.card block.Fibre = 8)
    (q e : ℕ) (hq : q.Prime) (hq11 : 11 ≤ q) (he : 1 ≤ e)
    (hqdiv : q ^ e ∣ blocks block)
    (hqmax : ¬ q ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P q e 1344 hq he hqdiv hqmax (by norm_num)
  · exact component_card_dvd_1344 block P hr
  · apply smallAffine_largePrime_margin 8 (blocks block) w
      block.degrees_ge_two.2 (by simpa only [hr] using width_eq block)
      (887 / 224) _ (Or.inr (Or.inl ⟨rfl, rfl⟩))
    exact refinedBudget_thirteenFortyFour_traceyPrimary_largePrime
      (blocks block) q e hq hq11 he

/-- Local degree nine, with a prime divisor at least eleven in the actual
block count. -/
noncomputable def of_degreeNine_largePrime
    (hr : Nat.card block.Fibre = 9)
    (q e : ℕ) (hq : q.Prime) (hq11 : 11 ≤ q) (he : 1 ≤ e)
    (hqdiv : q ^ e ∣ blocks block)
    (hqmax : ¬ q ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P q e 432 hq he hqdiv hqmax (by norm_num)
  · exact component_card_dvd_432 block P hr
  · apply smallAffine_largePrime_margin 9 (blocks block) w
      block.degrees_ge_two.2 (by simpa only [hr] using width_eq block)
      (115 / 32) _ (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    exact refinedBudget_fourThirtyTwo_traceyPrimary_largePrime
      (blocks block) q e hq hq11 he

/-- Local degree sixteen, with a prime divisor at least eleven in the actual
block count. -/
noncomputable def of_degreeSixteen_largePrime
    (hr : Nat.card block.Fibre = 16)
    (q e : ℕ) (hq : q.Prime) (hq11 : 11 ≤ q) (he : 1 ≤ e)
    (hqdiv : q ^ e ∣ blocks block)
    (hqmax : ¬ q ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P q e 322560 hq he hqdiv hqmax (by norm_num)
  · exact component_card_dvd_322560 block P hr
  · apply smallAffine_largePrime_margin 16 (blocks block) w
      block.degrees_ge_two.2 (by simpa only [hr] using width_eq block)
      (11689 / 1680) _ (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    exact refinedBudget_threeTwentyTwoFiveSixty_traceyPrimary_largePrime
      (blocks block) q e hq hq11 he

end ComponentSource
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
