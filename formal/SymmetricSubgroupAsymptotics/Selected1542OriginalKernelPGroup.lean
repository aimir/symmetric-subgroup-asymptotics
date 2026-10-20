import SymmetricSubgroupAsymptotics.Selected1542OriginalTargetMaps
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Coset.Card

/-! Exact graph and kernel cardinalities prove the actual original cubic
kernel is a binary group. No closure of the original group is enumerated. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

local instance : Fintype originalPreimage := Fintype.ofFinite _
local instance : originalPreimage.subtype.range.Normal := by
  rw [Subgroup.range_subtype]
  infer_instance

private theorem targetStateElement_bijective : Function.Bijective targetStateElement := by
  constructor
  · intro i j h
    apply actualQuotientGraph.target_word_injective
    exact congrArg Subtype.val h
  · exact actualQuotientGraph.certificate.sourceElement_surjective

theorem literalTarget_card : Nat.card literalTarget=48 := by
  have he : Fin 48 ≃ literalTarget := Equiv.ofBijective targetStateElement targetStateElement_bijective
  simpa only [Nat.card_fin] using (Nat.card_congr he).symm

theorem originalPreimage_card : Nat.card originalPreimage=64 := by
  simpa only [Nat.card_fin] using (Nat.card_congr preimageTable.chartEquiv).symm

theorem original_card : Nat.card Original=3072 := by
  have hquot : Nat.card (Original ⧸ originalPreimage)=48 := by
    have h := Nat.card_congr originalQuotientEquiv.toEquiv
    simpa only [Subgroup.range_subtype,literalTarget_card] using h
  calc
    Nat.card Original=Nat.card (Original ⧸ originalPreimage)*Nat.card originalPreimage :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup originalPreimage
    _=3072 := by rw [hquot,originalPreimage_card]

theorem originalBinaryKernel_card : Nat.card originalBinaryKernel=1024 := by
  have hquot : Nat.card (Original ⧸ originalBinaryKernel)=3 := by
    have h := Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective originalCubic originalCubic_surjective).toEquiv
    have hc : Nat.card CyclicThree=3 := by
      rw [Nat.card_congr (Multiplicative.toAdd : CyclicThree ≃ ZMod 3),Nat.card_zmod]
    simpa only [originalBinaryKernel,hc] using h
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup originalBinaryKernel
  rw [original_card,hquot] at h
  omega

theorem originalBinaryKernel_isPGroup : IsPGroup 2 originalBinaryKernel := by
  apply IsPGroup.of_card (n := 10)
  exact originalBinaryKernel_card

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
