import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleParabolicCardinality
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterAssociatedImage
import Mathlib.GroupTheory.Index

/-! Two actual disjoint Bruhat cells give the outer parabolic lower
bound, including the binary parameter. Its already constructed associated
image has at most six elements at zero, so the literal normal graded
two-kernel has at least2048 elements. No containment of this kernel in the
derived group or in the positive subgroup is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterParabolicCardinality
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFieldParameters
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedBorelCardinality
open CFSGReeFFourOuterParabolicFlag CFSGReeFFourOuterFixedInversion
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourRelativeSimpleWeyl
open CFSGReeFFourOriginalInversionFactors CFSGReeFFourOriginalNegativeStability
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourFixedSubgroupPeeling
open CFSGReeFFourFixedAmbientHom CFSGTwoBruhatCellsCardinality
open CFSGReeFFourOuterGradedQuotient CFSGReeFFourBinaryOuterAssociatedImage

private instance fixedFinite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

private theorem outer_inversion_le_positive (m : ℕ) :
    fixedOuterInversion m ≤ fixedPositive m := by
  intro x hx
  exact (show x.val ∈ modelInversion m (outerRelativeWeyl m) from hx).1

private theorem outer_inversion_to_negative (m : ℕ) (x : fixedOuterInversion m) :
    outerFixedWeyl m * x.val * (outerFixedWeyl m)⁻¹ ∈ fixedNegative m :=
  x.property.2

private theorem outer_inversion_card_ne_one (m : ℕ) : Nat.card (fixedOuterInversion m) ≠ 1 := by
  intro he
  rw [fixedOuterInversion_card] at he
  have hq : 2 ≤ 2^(2*m+1) :=
    (by decide : 2 ≤ (2 : ℕ)^1).trans (Nat.pow_le_pow_right (by decide) (by omega))
  omega

theorem outerFixedWeyl_not_mem_borel (m : ℕ) : outerFixedWeyl m ∉ fixedBorel m :=
  word_not_mem_of_nontrivial_inversion (fixedBorel m) (fixedPositive m) (fixedNegative m)
    (fixedOuterInversion m) (outerFixedWeyl m) (fixedBorel_le_normalizer m)
    (outer_inversion_le_positive m) (fixed_positive_negative_disjoint m)
    (outer_inversion_to_negative m) (outer_inversion_card_ne_one m)

theorem outerParabolic_card_lower (m : ℕ) :
    (2^(2*m+1))^12 * (2^(2*m+1)-1)^2 * (1+2^(2*m+1)) ≤
      Nat.card (outerParabolic m) := by
  have hBP : fixedBorel m ≤ outerParabolic m := by
    rw [fixedBorel_eq_sup]
    exact le_sup_left
  have hWP : outerFixedWeyl m ∈ outerParabolic m :=
    (show Subgroup.closure {outerFixedWeyl m} ≤ outerParabolic m from le_sup_right)
      (Subgroup.subset_closure (Set.mem_singleton_iff.mpr rfl))
  have h := card_mul_one_add_le (fixedBorel m) (fixedNegative m) (fixedOuterInversion m)
    (outerParabolic m) (outerFixedWeyl m)
    ((outer_inversion_le_positive m).trans (positive_le_borel m)) hBP hWP
    (fixedBorel_negative_disjoint m) (outerFixedWeyl_not_mem_borel m)
    (outer_inversion_to_negative m)
  rw [fixedBorel_card, fixedOuterInversion_card] at h
  exact h

theorem outerParabolic_zero_card_lower : 12288 ≤ Nat.card (outerParabolic 0) := by
  have h := outerParabolic_card_lower 0
  norm_num at h
  exact h

theorem gradedKernel_zero_card_lower : 2048 ≤ Nat.card (gradedKernel 0) := by
  have hc : Nat.card (gradedKernel 0) * Nat.card (outerAssociatedHom 0).range =
      Nat.card (outerParabolic 0) := by
    have h := (outerAssociatedHom 0).ker.card_mul_index
    rw [Subgroup.index_ker, outerAssociatedHom_ker] at h
    exact h
  have hprod : 2048 * 6 ≤ Nat.card (gradedKernel 0) * 6 := by
    calc
      _ ≤ Nat.card (outerParabolic 0) := outerParabolic_zero_card_lower
      _ = Nat.card (gradedKernel 0) * Nat.card (outerAssociatedHom 0).range := hc.symm
      _ ≤ _ := Nat.mul_le_mul_left _ image_card_le_six
  exact Nat.le_of_mul_le_mul_right hprod (by decide : 0 < (6 : ℕ))

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterParabolicCardinality
