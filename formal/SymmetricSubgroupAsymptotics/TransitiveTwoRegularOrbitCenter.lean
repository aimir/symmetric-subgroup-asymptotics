import SymmetricSubgroupAsymptotics.TransitiveTwoRegularOrbitChart

/-! Central elements in the literal two-regular-orbit chart.

When the actual normal subgroup is larger than one regular orbit image,
a central element cannot exchange the two orbits. Inside that normal
subgroup, centrality forces equal translation coordinates. The original
outside square is unrestricted throughout.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.TransitiveTwoRegularOrbitChart

open PermutationBinaryTwoOrbitSplit

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X] (H : Subgroup G) [H.Normal]
    (o₁ o₂ : MulAction.orbitRel.Quotient H X)
    (x₀ : o₁.orbit)
    (hregular : MulAction.stabilizer (TranslationGroup H o₁) x₀=⊥)
    (hne : o₁≠o₂)
    (hcover : ∀ o : MulAction.orbitRel.Quotient H X,o=o₁ ∨ o=o₂)

include o₂ x₀ hregular hne hcover in
/-- If a central element swapped the original orbits, either regular
coordinate alone would recover all of H. The strict original cardinal
inequality excludes that possibility. -/
theorem center_le_normal_of_translation_card
    (hindex : H.index=2)
    (hclasses : Nat.card (MulAction.orbitRel.Quotient H X)=2)
    (hlarge : Nat.card (TranslationGroup H o₁)<Nat.card H) :
    Subgroup.center G≤H := by
  intro z hz
  by_contra hzH
  have hzo : z • o₁.orbit=o₂.orbit :=
    not_mem_swaps_orbits_of_index_two H hindex hclasses o₁ o₂ hcover z hzH
  have hinj := translationPair_injective H o₁ o₂ x₀ hregular z hzo hne hcover
  have hdiag (h : H) :
      (translationPair H o₁ z h).2=(translationPair H o₁ z h).1 := by
    have he : MulAut.conjNormal z⁻¹ h=h := by
      apply Subtype.ext
      change z⁻¹*(h:G)*(z⁻¹)⁻¹=(h:G)
      rw [inv_inv,mul_assoc,Subgroup.mem_center_iff.mp hz (h:G)]
      simp only [← mul_assoc,inv_mul_cancel,one_mul]
    change (MulAction.toPermHom H o₁.orbit).rangeRestrict (MulAut.conjNormal z⁻¹ h)=
      (MulAction.toPermHom H o₁.orbit).rangeRestrict h
    rw [he]
  have hfirst : Function.Injective
      (fun h : H => (translationPair H o₁ z h).1) := by
    intro a b hab
    apply hinj
    exact Prod.ext hab ((hdiag a).trans (hab.trans (hdiag b).symm))
  have hc := Nat.card_le_card_of_injective _ hfirst
  omega

variable (g : G) (hg : g • o₁.orbit=o₂.orbit)

include x₀ hregular hne hcover hg in
/-- A central original element lying in H has literally identical
translation coordinates in the transported regular point chart. -/
theorem central_translationPair_diagonal (z : H)
    (hz : (z:G)∈Subgroup.center G) :
    (translationPair H o₁ g z).1=(translationPair H o₁ g z).2 := by
  let e := pointChart H o₁ o₂ x₀ hregular g hg hne hcover
  have he : (z:G) • (g • e (Sum.inl 1))=
      g • ((z:G) • e (Sum.inl 1)) := by
    simp only [← mul_smul]
    rw [Subgroup.mem_center_iff.mp hz g]
  change (z:G) • pointChart H o₁ o₂ x₀ hregular g hg hne hcover (Sum.inr 1)=
    g • ((z:G) • pointChart H o₁ o₂ x₀ hregular g hg hne hcover (Sum.inl 1)) at he
  rw [normal_action_inr,normal_action_inl,outside_action_inl] at he
  have hp := Sum.inr.inj (e.injective he)
  simpa only [mul_one] using hp.symm

end SymmetricSubgroupAsymptotics.TransitiveTwoRegularOrbitChart
