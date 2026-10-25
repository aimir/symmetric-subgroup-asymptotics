import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareCommutator
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryAbelianGenerators
import SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedPositiveCardLower
import SymmetricSubgroupAsymptotics.FiniteCyclicNormalizerProduct

/-! The actual middle-square commutator reduces every binary abelian
image to at most four elements. Its literal positive/derived intersection
and faithful Tits image therefore have at least 1024 elements. No derived
index-two assertion or two-Sylow generation is used or claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMiddleSquareSaving
open CFSGReeFFourMiddleSquareCommutator CFSGReeFFourBinaryAbelianGenerators
open CFSGReeFFourDerivedPositiveCardLower CFSGReeFFourAllParameterDerivedPositive
open CFSGReeFFourFixedAmbientHom CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourOuterThreeWord CFSGReeFFourDerivedAmbientHom

private instance fixed_finite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

theorem square_image_one {B : Type*} [CommGroup B] (m : ℕ)
    (f : originalModelFixed m →* B) : (f (fourCycle m))^2 = 1 := by
  have h := (Abelianization.commutator_subset_ker f) (square_mem_derived m)
  change f ((fourCycle m)^2) = 1 at h
  simpa only [map_pow] using h

private theorem finite_range_card_le_four {B : Type*} [CommGroup B] [Finite B]
    (f : originalModelFixed 0 →* B) : Nat.card f.range ≤ 4 := by
  rw [range_eq_two_zpowers]
  refine FiniteCyclicNormalizerProduct.card_join_le_mul
    (f (outerInvolution 0)) (f (fourCycle 0)) 1 ?_ 2 2
      (by decide) (by decide) ?_ (square_image_one 0 f)
  · rw [pow_one,mul_comm (f (fourCycle 0)) (f (outerInvolution 0)),
      mul_assoc,mul_inv_cancel,mul_one]
  · rw [←map_pow,outerInvolution_square,map_one]

theorem range_card_le_four {B : Type*} [CommGroup B]
    (f : originalModelFixed 0 →* B) : Nat.card f.range ≤ 4 := by
  letI : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have h := finite_range_card_le_four f.rangeRestrict
  rw [MonoidHom.range_eq_top.mpr f.rangeRestrict_surjective,Subgroup.card_top] at h
  exact h

theorem abelianization_card_le_four :
    Nat.card (Abelianization (originalModelFixed 0)) ≤ 4 := by
  let f : originalModelFixed 0 →* Abelianization (originalModelFixed 0) := Abelianization.of
  have hf : Function.Surjective f :=
    QuotientGroup.mk'_surjective (commutator (originalModelFixed 0))
  have h := range_card_le_four f
  rw [MonoidHom.range_eq_top.mpr hf,Subgroup.card_top] at h
  exact h

theorem derivedPositive_card_ge_1024 : 1024 ≤ Nat.card (derivedPositive 0) := by
  let I : Subgroup (Abelianization (originalModelFixed 0)) :=
    (fixedPositive 0).map Abelianization.of
  have hI : Nat.card I ≤ 4 :=
    (Nat.card_le_card_of_injective I.subtype Subtype.val_injective).trans
      abelianization_card_le_four
  have hc : Nat.card (derivedPositive 0)*Nat.card I = 4096 :=
    (derivedPositive_card_factor 0).trans (by decide)
  have h := Nat.mul_le_mul_left (Nat.card (derivedPositive 0)) hI
  rw [hc] at h
  omega

theorem tits_positive_image_card_ge_1024 : 1024 ≤ Nat.card titsPositiveHom.range := by
  have he : Nat.card (derivedPositive 0) = Nat.card titsPositiveHom.range :=
    Nat.card_congr (MonoidHom.ofInjective titsPositiveHom_injective).toEquiv
  exact derivedPositive_card_ge_1024.trans_eq he

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMiddleSquareSaving
