import SymmetricSubgroupAsymptotics.CFSGReeFFourAbelianImageCardinality
import SymmetricSubgroupAsymptotics.CFSGReeFFourAllParameterDerivedPositive
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveCardinality
import SymmetricSubgroupAsymptotics.ExactHomSubgroupCardinality
import Mathlib.GroupTheory.Abelianization.Finite

/-! A lower bound on the literal SAME positive/derived intersection.
The exact kernel/image factorization of the abelianization map charges its
image by the proved q³ bound and its source by the actual q¹² cardinality.
At zero the retained intersection and its faithful image in Tits have at
least 512 elements. No derived-index-two assertion is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedPositiveCardLower
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedAmbientHom CFSGReeFFourDerivedAmbientHom
open CFSGReeFFourAbelianImageCardinality CFSGReeFFourFixedPositiveCardinality
open CFSGReeFFourAllParameterDerivedPositive

private instance fixed_finite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

theorem derivedPositive_card_factor (m : ℕ) :
    Nat.card (derivedPositive m) *
      Nat.card ((fixedPositive m).map
        (Abelianization.of : originalModelFixed m →* Abelianization (originalModelFixed m))) =
      (2^(2*m+1))^12 := by
  let f : originalModelFixed m →* Abelianization (originalModelFixed m) := Abelianization.of
  let D : Subgroup (originalModelFixed m) := commutator (originalModelFixed m)
  have he : D.subtype.range = f.ker :=
    D.range_subtype.trans (Abelianization.ker_of (originalModelFixed m)).symm
  have hc := ExactHomSubgroupCardinality.card_comap_mul_card_map f D.subtype
    Subtype.val_injective he (fixedPositive m)
  exact hc.trans (fixedPositive_card m)

theorem derivedPositive_card_lower (m : ℕ) :
    (2^(2*m+1))^9 ≤ Nat.card (derivedPositive m) := by
  let I : Subgroup (Abelianization (originalModelFixed m)) :=
    (fixedPositive m).map Abelianization.of
  have hI : Nat.card I ≤ (2^(2*m+1))^3 :=
    (Nat.card_le_card_of_injective I.subtype Subtype.val_injective).trans
      (abelianization_card_le m)
  have hc : Nat.card (derivedPositive m) * Nat.card I = (2^(2*m+1))^12 :=
    derivedPositive_card_factor m
  have hprod : (2^(2*m+1))^9 * (2^(2*m+1))^3 ≤
      Nat.card (derivedPositive m) * (2^(2*m+1))^3 := by
    calc
      _ = (2^(2*m+1))^12 := by ring
      _ = Nat.card (derivedPositive m) * Nat.card I := hc.symm
      _ ≤ _ := Nat.mul_le_mul_left _ hI
  exact Nat.le_of_mul_le_mul_right hprod (pow_pos (pow_pos (by decide) _) _)

theorem tits_positive_card_lower : 512 ≤ Nat.card (derivedPositive 0) := by
  have h := derivedPositive_card_lower 0
  norm_num at h
  exact h

theorem tits_positive_image_card_lower : 512 ≤ Nat.card titsPositiveHom.range := by
  have he : Nat.card (derivedPositive 0) = Nat.card titsPositiveHom.range :=
    Nat.card_congr (MonoidHom.ofInjective titsPositiveHom_injective).toEquiv
  exact tits_positive_card_lower.trans_eq he

end SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedPositiveCardLower
