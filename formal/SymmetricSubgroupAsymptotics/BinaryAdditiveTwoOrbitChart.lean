import SymmetricSubgroupAsymptotics.BinaryRegularFourCoordinates
import SymmetricSubgroupAsymptotics.TransitiveTwoRegularOrbitCenter

/-! An additive chart constructed from the original two regular orbits.

All equations in the chart are consequences of the literal regular
image and the original point action. The original outside element is
used to transport the second orbit; no outside-square or splitting
hypothesis is introduced.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics

variable {G X : Type} [Group G] [MulAction G X]

/-- A chart on the original points, including only proved structural
facts needed by the nonzero-twist argument. -/
structure BinaryAdditiveTwoOrbitChart (H : Subgroup G) where
  chart : BinaryRegularFourSpace ⊕ BinaryRegularFourSpace ≃ X
  coordinate : H → BinaryRegularFourSpace
  coordinate_surjective : Function.Surjective coordinate
  normal_left : ∀ h : H,∀ v,
    (h:G) • chart (Sum.inl v)=chart (Sum.inl (coordinate h+v))
  central_diagonal : ∀ t : G,t∈Subgroup.center G →
    ∃ δ : BinaryRegularFourSpace,
      (∀ v,t • chart (Sum.inl v)=chart (Sum.inl (δ+v))) ∧
      (∀ v,t • chart (Sum.inr v)=chart (Sum.inr (δ+v)))
  fixed_left : ∀ f∈(permutationFunctionRepresentation (ZMod 2) H X).invariants,∀ v,
    f (chart (Sum.inl v))=f (chart (Sum.inl 0))

namespace BinaryAdditiveTwoOrbitChart

open TransitiveTwoRegularOrbitChart

variable [Finite G] [Finite X] [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    (H : Subgroup G) [H.Normal]
    (o₁ o₂ : MulAction.orbitRel.Quotient H X) (x₀ : o₁.orbit)
    (hregular : MulAction.stabilizer (TranslationGroup H o₁) x₀=⊥)
    (hne : o₁≠o₂)
    (hcover : ∀ o : MulAction.orbitRel.Quotient H X,o=o₁ ∨ o=o₂)
    (hindex : H.index=2)
    (hclasses : Nat.card (MulAction.orbitRel.Quotient H X)=2)
    (hcard : Nat.card (TranslationGroup H o₁)=4)
    (hsquare : ∀ v : TranslationGroup H o₁,v^2=1)
    (hlarge : 4<Nat.card H)

/-- Construct every chart equation from the actual regular image. -/
def ofRegularOrbits : BinaryAdditiveTwoOrbitChart (X := X) H := by
  let g := (PermutationBinaryTwoOrbitSplit.exists_orbit_translation H o₁ o₂).choose
  have hg : g • o₁.orbit=o₂.orbit :=
    (PermutationBinaryTwoOrbitSplit.exists_orbit_translation H o₁ o₂).choose_spec
  let c := binaryFourCoordinates hcard hsquare
  let q : BinaryRegularFourSpace ≃ TranslationGroup H o₁ :=
    Multiplicative.ofAdd.trans c.symm.toEquiv
  let e₀ := pointChart H o₁ o₂ x₀ hregular g hg hne hcover
  let e : BinaryRegularFourSpace ⊕ BinaryRegularFourSpace ≃ X := (Equiv.sumCongr q q).trans e₀
  let first : H → BinaryRegularFourSpace := fun h => (c (translationPair H o₁ g h).1).toAdd
  let second : H → BinaryRegularFourSpace := fun h => (c (translationPair H o₁ g h).2).toAdd
  have hqadd (a : TranslationGroup H o₁) (v : BinaryRegularFourSpace) :
      q ((c a).toAdd+v)=a*q v := by
    change c.symm (Multiplicative.ofAdd ((c a).toAdd+v))=
      a*c.symm (Multiplicative.ofAdd v)
    apply c.injective
    rw [c.apply_symm_apply,map_mul,c.apply_symm_apply]
    rfl
  have hfirst : Function.Surjective first := by
    intro v
    obtain ⟨h,hh⟩ := translationPair_fst_surjective H o₁ g (q v)
    change (translationPair H o₁ g h).1=q v at hh
    refine ⟨h,?_⟩
    change (c (translationPair H o₁ g h).1).toAdd=v
    rw [hh]
    change (c (c.symm (Multiplicative.ofAdd v))).toAdd=v
    rw [c.apply_symm_apply]
    rfl
  have hleft (h : H) (v : BinaryRegularFourSpace) :
      (h:G) • e (Sum.inl v)=e (Sum.inl (first h+v)) := by
    change (h:G) • pointChart H o₁ o₂ x₀ hregular g hg hne hcover (Sum.inl (q v))=
      pointChart H o₁ o₂ x₀ hregular g hg hne hcover
        (Sum.inl (q ((c (translationPair H o₁ g h).1).toAdd+v)))
    rw [normal_action_inl,hqadd]
  have hright (h : H) (v : BinaryRegularFourSpace) :
      (h:G) • e (Sum.inr v)=e (Sum.inr (second h+v)) := by
    change (h:G) • pointChart H o₁ o₂ x₀ hregular g hg hne hcover (Sum.inr (q v))=
      pointChart H o₁ o₂ x₀ hregular g hg hne hcover
        (Sum.inr (q ((c (translationPair H o₁ g h).2).toAdd+v)))
    rw [normal_action_inr,hqadd]
  refine ⟨e,first,hfirst,hleft,?_,?_⟩
  · intro t ht
    have htH : t∈H := center_le_normal_of_translation_card
      H o₁ o₂ x₀ hregular hne hcover hindex hclasses (by rw [hcard]; exact hlarge) ht
    let h : H := ⟨t,htH⟩
    have hdiag : first h=second h := congrArg (fun v => (c v).toAdd)
      (central_translationPair_diagonal H o₁ o₂ x₀ hregular hne hcover g hg h ht)
    refine ⟨first h,hleft h,?_⟩
    intro v
    rw [hdiag]
    exact hright h v
  · intro f hf v
    obtain ⟨h,hh⟩ := hfirst v
    change first h=v at hh
    have he := congrFun (hf h⁻¹) (e (Sum.inl 0))
    change f ((((h⁻¹:H)⁻¹):G) • e (Sum.inl 0))=f (e (Sum.inl 0)) at he
    have he' : f ((h:G) • e (Sum.inl 0))=f (e (Sum.inl 0)) := by
      simpa only [Subgroup.coe_inv,inv_inv] using he
    rw [hleft,add_zero,hh] at he'
    exact he'

end BinaryAdditiveTwoOrbitChart

end SymmetricSubgroupAsymptotics
