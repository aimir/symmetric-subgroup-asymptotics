import SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketCommutator
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMiddleSquareSaving

/-! The actual whole-block inner commutator kills the outer character.
Together with the proved middle-square relation, the binary abelian image
has at most two elements. The literal positive/derived intersection and
its faithful Tits full-centre-quotient image have at least 2048 elements.
No simplicity, known derived index or two-Sylow generation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterSaving
open CFSGReeFFourInnerBracketCommutator CFSGReeFFourInnerBracketOriginalBlocks
open CFSGReeFFourBinaryMiddleSquareSaving CFSGReeFFourBinaryAbelianGenerators
open CFSGReeFFourOuterThreeWord CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedAmbientHom
open CFSGReeFFourDerivedPositiveCardLower CFSGReeFFourAllParameterDerivedPositive
open CFSGReeFFourDerivedAmbientHom

private instance fixed_finite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

theorem outer_image_one {B : Type*} [CommGroup B] (m : ℕ)
    (f : originalModelFixed m →* B) : f (outerInvolution m)=1 := by
  have h := (Abelianization.commutator_subset_ker f) (candidate_mem_derived m)
  change f (candidate m)=1 at h
  rw [candidate_image] at h
  exact h

theorem outer_mem_derived (m : ℕ) :
    outerInvolution m ∈ commutator (originalModelFixed m) := by
  rw [←Abelianization.ker_of (originalModelFixed m)]
  exact outer_image_one m Abelianization.of

private theorem finite_range_card_le_two {B : Type*} [CommGroup B] [Finite B]
    (f : originalModelFixed 0 →* B) : Nat.card f.range ≤ 2 := by
  rw [range_eq_two_zpowers]
  refine FiniteCyclicNormalizerProduct.card_join_le_mul
    (f (outerInvolution 0)) (f (fourCycle 0)) 1 ?_ 1 2
      (by decide) (by decide) ?_ (square_image_one 0 f)
  · simp only [outer_image_one,pow_one,mul_one,mul_inv_cancel]
  · rw [pow_one,outer_image_one]

theorem range_card_le_two {B : Type*} [CommGroup B]
    (f : originalModelFixed 0 →* B) : Nat.card f.range ≤ 2 := by
  letI : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have h := finite_range_card_le_two f.rangeRestrict
  rw [MonoidHom.range_eq_top.mpr f.rangeRestrict_surjective,Subgroup.card_top] at h
  exact h

theorem abelianization_card_le_two :
    Nat.card (Abelianization (originalModelFixed 0)) ≤ 2 := by
  let f : originalModelFixed 0 →* Abelianization (originalModelFixed 0) := Abelianization.of
  have hf : Function.Surjective f :=
    QuotientGroup.mk'_surjective (commutator (originalModelFixed 0))
  have h := range_card_le_two f
  rw [MonoidHom.range_eq_top.mpr hf,Subgroup.card_top] at h
  exact h

theorem derivedPositive_card_ge_2048 : 2048 ≤ Nat.card (derivedPositive 0) := by
  let I : Subgroup (Abelianization (originalModelFixed 0)) :=
    (fixedPositive 0).map Abelianization.of
  have hI : Nat.card I ≤ 2 :=
    (Nat.card_le_card_of_injective I.subtype Subtype.val_injective).trans
      abelianization_card_le_two
  have hc : Nat.card (derivedPositive 0)*Nat.card I=4096 :=
    (derivedPositive_card_factor 0).trans (by decide)
  have h := Nat.mul_le_mul_left (Nat.card (derivedPositive 0)) hI
  rw [hc] at h
  omega

theorem tits_positive_image_card_ge_2048 : 2048 ≤ Nat.card titsPositiveHom.range := by
  have he : Nat.card (derivedPositive 0)=Nat.card titsPositiveHom.range :=
    Nat.card_congr (MonoidHom.ofInjective titsPositiveHom_injective).toEquiv
  exact derivedPositive_card_ge_2048.trans_eq he

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterSaving
