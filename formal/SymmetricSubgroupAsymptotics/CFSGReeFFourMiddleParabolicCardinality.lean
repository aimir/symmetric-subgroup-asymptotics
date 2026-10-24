import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedBorelCardinality
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleParabolicFlag
import SymmetricSubgroupAsymptotics.CFSGTwoBruhatCellsCardinality
import SymmetricSubgroupAsymptotics.CFSGReeFFourWeightedFixedOrderUpper
import SymmetricSubgroupAsymptotics.CFSGReeFFourParabolicIndexNumerics

/-! Two disjoint actual cells inside the proper middle parabolic give
its order lower bound and hence its index upper bound. All source block,
normalizer and nontriviality premises are discharged here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleParabolicCardinality
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFieldParameters
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedBorelCardinality
open CFSGReeFFourMiddleParabolicFlag CFSGReeFFourMiddleFixedInversion
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourRelativeSimpleWeyl
open CFSGReeFFourOriginalInversionFactors CFSGReeFFourOriginalNegativeStability
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourFixedSubgroupPeeling
open CFSGReeFFourFixedAmbientHom CFSGTwoBruhatCellsCardinality
open CFSGReeFFourWeightedFixedOrderUpper CFSGReeFFourParabolicIndexNumerics

private instance fixed_finite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

private theorem middle_inversion_le_positive (m : ℕ) :
    fixedMiddleInversion m≤fixedPositive m := by
  intro x hx
  exact (show x.val∈modelInversion m (middleRelativeWeyl m) from hx).1

private theorem middle_inversion_to_negative (m : ℕ) (x : fixedMiddleInversion m) :
    middleFixedWeyl m*x.val*(middleFixedWeyl m)⁻¹∈fixedNegative m :=
  x.property.2

private theorem middle_inversion_card_ne_one (m : ℕ) : Nat.card (fixedMiddleInversion m)≠1 := by
  intro he
  rw [fixedMiddleInversion_card] at he
  have hq : 2≤2^(2*m+1) :=
    (by decide : 2≤(2 : ℕ)^1).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hpow := Nat.pow_le_pow_left hq 2
  rw [he] at hpow
  norm_num at hpow

theorem middleFixedWeyl_not_mem_borel (m : ℕ) : middleFixedWeyl m∉fixedBorel m :=
  word_not_mem_of_nontrivial_inversion (fixedBorel m) (fixedPositive m) (fixedNegative m)
    (fixedMiddleInversion m) (middleFixedWeyl m) (fixedBorel_le_normalizer m)
    (middle_inversion_le_positive m) (fixed_positive_negative_disjoint m)
    (middle_inversion_to_negative m) (middle_inversion_card_ne_one m)

theorem middleParabolic_card_lower (m : ℕ) :
    (2^(2*m+1))^12*(2^(2*m+1)-1)^2*(1+(2^(2*m+1))^2)≤Nat.card (middleParabolic m) := by
  have hBP : fixedBorel m≤middleParabolic m := by
    rw [fixedBorel_eq_sup]
    exact le_sup_left
  have hWP : middleFixedWeyl m∈middleParabolic m :=
    (show Subgroup.closure {middleFixedWeyl m}≤middleParabolic m from le_sup_right)
      (Subgroup.subset_closure (Set.mem_singleton_iff.mpr rfl))
  have h := card_mul_one_add_le (fixedBorel m) (fixedNegative m) (fixedMiddleInversion m)
    (middleParabolic m) (middleFixedWeyl m)
    ((middle_inversion_le_positive m).trans (positive_le_borel m)) hBP hWP
    (fixedBorel_negative_disjoint m) (middleFixedWeyl_not_mem_borel m)
    (middle_inversion_to_negative m)
  rw [fixedBorel_card,fixedMiddleInversion_card] at h
  exact h

theorem middleParabolic_index_le (m : ℕ) :
    (middleParabolic m).index ≤ indexUpper (2^(2*m+1)) := by
  have hq : 2≤2^(2*m+1) :=
    (by decide : 2≤(2 : ℕ)^1).trans (Nat.pow_le_pow_right (by decide) (by omega))
  apply index_le_of_card_bounds _ (Nat.card (middleParabolic m)) _ hq
    (middleParabolic_card_lower m)
  rw [Subgroup.card_mul_index]
  exact fixed_order_le_weighted m

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleParabolicCardinality
