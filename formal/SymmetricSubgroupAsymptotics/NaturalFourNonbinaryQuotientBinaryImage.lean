import SymmetricSubgroupAsymptotics.NaturalFourNormalClassification
import SymmetricSubgroupAsymptotics.SingleCubicNormalBinaryImage

/-! Actual binary normal images in the nonbinary normal quotients of
the literal natural A4 and S4 lie in the genuine Klein image. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NaturalFourNonbinaryQuotientBinaryImage

theorem symmetric_preimage_le {Q : Type} [Group Q] [Finite Q]
    (f : Equiv.Perm (Fin 4) →* Q) (hf : Function.Surjective f)
    (hQ : 3∣Nat.card Q) (L : Subgroup Q) (hL : L.Normal)
    (hb : IsPGroup 2 L) : L.comap f≤NaturalS4.klein := by
  apply SingleCubicNormalBinaryImage.preimage_le f hf 3 (by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]; norm_num)
    hQ NaturalS4.klein _ L hL hb
  intro M hm
  rcases NaturalFourNormalClassification.normal_four_cases M hm with h | h | h | h
  · left; rw [h]; exact bot_le
  · left; rw [h]
  · right; rw [h,alternatingGroup.card_of_card_eq_four (by simp)]; norm_num
  · right; rw [h,Nat.card_congr Subgroup.topEquiv.toEquiv,
      Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]; norm_num

theorem alternating_preimage_le {Q : Type} [Group Q] [Finite Q]
    (f : alternatingGroup (Fin 4) →* Q) (hf : Function.Surjective f)
    (hQ : 3∣Nat.card Q) (L : Subgroup Q) (hL : L.Normal)
    (hb : IsPGroup 2 L) : L.comap f≤alternatingGroup.kleinFour (Fin 4) := by
  apply SingleCubicNormalBinaryImage.preimage_le f hf 2
    (by rw [alternatingGroup.card_of_card_eq_four (by simp)]; norm_num)
    hQ (alternatingGroup.kleinFour (Fin 4)) _ L hL hb
  intro M hm
  rcases NaturalA4ScalarFourHead.normal_subgroup_trichotomy M hm with h | h | h
  · left; rw [h]; exact bot_le
  · left; rw [h]
  · right; rw [h,Nat.card_congr Subgroup.topEquiv.toEquiv,
      alternatingGroup.card_of_card_eq_four (by simp)]; norm_num

end SymmetricSubgroupAsymptotics.NaturalFourNonbinaryQuotientBinaryImage
