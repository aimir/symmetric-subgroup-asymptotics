import SymmetricSubgroupAsymptotics.ActualWreathAffineSixCapacity
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeRegularSixSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeCoefficient
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeResidualAssembly

/-!
# Close the regular degree-three component over six blocks

The actual correlated ternary translation kernel embeds in the module
induced from one literal block.  Restriction to an actual Sylow-three
subgroup and the integer Mackey width at index six sharpen every section's
Schur capacity from the generic value three to two.  This file installs that
sharp capacity in the already checked top-translation endpoint.

The finite incidence coefficient is unchanged.  In particular, this is not
an independent replacement of the actual block system by a degree-six
catalogue action.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The literal translation capacity with the six-block Sylow/Mackey
section bound installed.  Only the capacity field changes; the joint
fixed-top coefficient and all retained normal-section fibres are inherited
from `translationLayerJointCapacity`. -/
noncomputable def degreeThreeRegularSixJointCapacity
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 6) :
    ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  let H := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm
  have hpd := degreeThree_translation_prime_dim block P hr
  let i₀ : block.Points := Classical.choice inferInstance
  exact ActualWreathAffineCapacity.sharpenJointCapacityToTwo_of_ternary_six
    S (localMap block P) C H hpd.1 hpd.2
      (by simpa only [Fintype.card_eq_nat_card] using hs) i₀

@[simp] theorem degreeThreeRegularSixJointCapacity_capacity
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 6) :
    (degreeThreeRegularSixJointCapacity block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm hr hs).capacity = 2 := rfl

@[simp] theorem degreeThreeRegularSixJointCapacity_coefficient
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 6) :
    (degreeThreeRegularSixJointCapacity block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm hr hs).coefficient =
      (translationLayerJointCapacity block P hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm).coefficient := rfl

/-- The regular-C3, six-block cell has a complete ambient source.  The
terminal action is the faithful action on the six actual blocks; the sharp
capacity is two and the original ternary incidence coefficient is paid by
the common degree-three coefficient theorem. -/
noncomputable def degreeThreeRegularSixSource
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 6)
    (hcomponent : Nat.card block.Component ∣ 3) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let H₀ := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm
  let H := degreeThreeRegularSixJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm hr hs
  have hpd := degreeThree_translation_prime_dim block P hr
  have hs2 : 2 ≤ Nat.card block.Points := block.degrees_ge_two.2
  have hw : w = 3 * Nat.card block.Points := by
    simpa only [hr] using width_eq block
  have hcoeff₀ := translationLayerJointCapacity_coefficient_le block P
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
  have hp : P.p = 3 := by
    simpa only [localTranslationChart] using hpd.1
  have hcoeff : H₀.coefficient ≤ (3 : ℝ) ^
      traceyAffineCoefficientExponent 1 (Nat.card block.Points)
        (traceyInducedGeneratorCeiling 1 (Nat.card block.Points))
        (traceyPermutationGeneratorCeiling w) w 3 := by
    simpa only [H₀, hpd.1, hpd.2, hp, Fintype.card_eq_nat_card] using hcoeff₀
  have hD₀ := degreeThreeTranslationCoefficient_bound
    (Nat.card block.Points) w hs2 hw H₀.coefficient hcoeff
  have hD : ∀ b : ℕ, H.coefficient ≤
      (2 : ℝ) ^ (affineComponentWidthCost w +
        8 * (w : ℝ) * Real.logb 2 (b + 1)) := by
    intro b
    simpa only [H, degreeThreeRegularSixJointCapacity_coefficient, H₀] using
      hD₀ b
  have hlocal : ∀ q : LocalQuotient block P, q = 1 :=
    degreeThree_localQuotient_eq_one_of_component_dvd_three
      block P hr hcomponent
  have hm : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - Nat.card block.Points) / 8 -
        Real.logb 2 (elementaryChart block P).p /
          (elementaryChart block P).p * H.capacity := by
    have hw18 : w = 18 := by
      simpa only [hs] using hw
    have hwR : (w : ℝ) = 18 := by exact_mod_cast hw18
    have heven : evenWidth w = 18 := by
      rw [hw18]
      norm_num [evenWidth, halfDegree]
    have hsR : (Nat.card block.Points : ℝ) = 6 := by exact_mod_cast hs
    have hep : (elementaryChart block P).p = 3 := by
      simpa only [elementaryChart, localTranslationChart] using hpd.1
    have hHcap : H.capacity = 2 := by
      exact degreeThreeRegularSixJointCapacity_capacity block P
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hs
    have hlog2 : Real.logb 2 3 ≤ 2 := by
      have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 4)
      simpa [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
        Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h
    rw [hwR, heven, hsR, hHcap, hep]
    norm_num [preE7CharacterRho]
    linarith
  exact topTranslationLayerSource block P hlocal H hs2 hm hD

/-- The required residual-lane function, with no project-owned premise. -/
noncomputable def degreeThreeRegularSixResidualSource
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    DegreeThreeRegularSixResidualSource := by
  intro w U hw basePoint block P hres hr hs hcomponent
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  exact degreeThreeRegularSixSource block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm hr hs hcomponent

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
