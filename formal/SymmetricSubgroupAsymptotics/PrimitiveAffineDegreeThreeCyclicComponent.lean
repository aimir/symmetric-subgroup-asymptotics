import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveDegreeThreeExhaustion

/-!
# Cyclic degree-three affine components in the exceptional block cells

When the literal degree-three affine component has order dividing three, its
entire local chief budget is a single ternary factor.  The integral Tracey
rates then close four of the six residual block counts directly.  Thus these
cells never need an ambient small-action classification.
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

private theorem gamma_nonneg : 0 ≤ fixedTargetCompositionGamma := by
  exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)

private theorem cyclic_budget_three :
    integralRefinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimePowerRate 3 1) 3 =
      fixedTargetCompositionGamma := by
  rw [show 3 = 3 ^ 1 by norm_num,
    integralRefinedWeightedFactorBudget_prime_pow _
      (by norm_num : Nat.Prime 3)]
  simp [ActualWreathCompressionTower.traceyPrimePowerRate, Nat.choose]
  norm_num [fixedTargetCompositionGamma]

private theorem cyclic_budget_four :
    integralRefinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimePowerRate 2 2) 3 =
      fixedTargetCompositionGamma := by
  rw [show 3 = 3 ^ 1 by norm_num,
    integralRefinedWeightedFactorBudget_prime_pow _
      (by norm_num : Nat.Prime 3)]
  simp [ActualWreathCompressionTower.traceyPrimePowerRate]
  unfold fixedTargetCompositionGamma
  ring

private theorem cyclic_budget_twelve :
    integralRefinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate 12 2 2) 3 =
      3 * fixedTargetCompositionGamma := by
  rw [show 3 = 3 ^ 1 by norm_num,
    integralRefinedWeightedFactorBudget_prime_pow _
      (by norm_num : Nat.Prime 3)]
  simp [ActualWreathCompressionTower.traceyPrimaryRate]
  unfold fixedTargetCompositionGamma
  ring

private theorem cyclic_budget_eighteen :
    integralRefinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate 18 3 2) 3 ≤
      7 * fixedTargetCompositionGamma := by
  rw [show 3 = 3 ^ 1 by norm_num,
    integralRefinedWeightedFactorBudget_prime_pow _
      (by norm_num : Nat.Prime 3)]
  have hrate := traceyPrimaryRate_three_matching_of_two_le 18 2 (by norm_num)
  have hrate0 :=
    ActualWreathCompressionTower.traceyPrimaryRate_nonneg 18 3 2 3
  have hfloor : Nat.floor
      (ActualWreathCompressionTower.traceyPrimaryRate 18 3 2 3) ≤ 7 := by
    apply Nat.lt_succ_iff.mp
    apply (Nat.floor_lt hrate0).mpr
    norm_num at hrate ⊢
    linarith
  have hfloorR : (Nat.floor
      (ActualWreathCompressionTower.traceyPrimaryRate 18 3 2 3) : ℝ) ≤ 7 := by
    exact_mod_cast hfloor
  have hgamma0 : 0 ≤ Real.logb 2 3 / 3 :=
    div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  unfold fixedTargetCompositionGamma
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hfloorR hgamma0

noncomputable def of_degreeThree_threeBlocks_cyclic
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 3)
    (hcomponent : Nat.card block.Component ∣ 3) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_integralTraceyPrimePower hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm block P 3 1 3 (by norm_num) (by norm_num) hs (by norm_num)
      hcomponent
  rw [cyclic_budget_three]
  have hw : w = 9 := by simpa only [hr, hs] using width_eq block
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  rw [hs]
  norm_num [hw, preE7CharacterRho, evenWidth, halfDegree] at hgamma ⊢
  linarith

noncomputable def of_degreeThree_fourBlocks_cyclic
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component ∣ 3) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_integralTraceyPrimePower hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm block P 2 2 3 (by norm_num) (by norm_num) hs (by norm_num)
      hcomponent
  rw [cyclic_budget_four]
  have hw : w = 12 := by simpa only [hr, hs] using width_eq block
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  rw [hs]
  norm_num [hw, preE7CharacterRho, evenWidth, halfDegree] at hgamma ⊢
  linarith

noncomputable def of_degreeThree_twelveBlocks_cyclic
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 12)
    (hcomponent : Nat.card block.Component ∣ 3) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_integralTraceyPrimary hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm block P 2 2 3 (by norm_num) (by norm_num)
      (by rw [hs]; norm_num) (by rw [hs]; norm_num) (by norm_num) hcomponent
  rw [hs, cyclic_budget_twelve]
  have hw : w = 36 := by simpa only [hr, hs] using width_eq block
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  norm_num [hw, preE7CharacterRho, evenWidth, halfDegree] at hgamma ⊢
  linarith

noncomputable def of_degreeThree_eighteenBlocks_cyclic
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 18)
    (hcomponent : Nat.card block.Component ∣ 3) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_integralTraceyPrimary hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm block P 3 2 3 (by norm_num) (by norm_num)
      (by rw [hs]; norm_num) (by rw [hs]; norm_num) (by norm_num) hcomponent
  have hw : w = 54 := by simpa only [hr, hs] using width_eq block
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hbudget := cyclic_budget_eighteen
  rw [hs]
  norm_num [hw, preE7CharacterRho, evenWidth, halfDegree] at hgamma ⊢
  linarith

end ComponentSource
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
