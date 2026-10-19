import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers

/-! A normal subgroup on which an actual quotient projection is injective
costs no more than its actual image. This is not subgroup monotonicity. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

 theorem normalGen_le_image_of_disjoint_kernel
    {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Surjective f)
    (S : Subgroup G) [S.Normal] (hdisjoint : S ⊓ f.ker=⊥) :
    MarkedC4.normalGen S≤MarkedC4.normalGen (S.map f) := by
  letI : (S.map f).Normal := Subgroup.Normal.map inferInstance f hf
  obtain ⟨b,hcard,hb,hclosure⟩ := MarkedC4.normalGen_spec (S.map f)
  have hker : ∀ x∈S, f x=1 → x∈(⊥ : Subgroup G) := by
    intro x hx hfx
    have hmem : x∈S ⊓ f.ker := ⟨hx,hfx⟩
    rwa [hdisjoint] at hmem
  obtain ⟨c,hcCard,hcS,hcStep⟩ :=
    MarkedC4.exists_layer_lift f hf ⊥ S hker b hb hclosure
  have hcClosure : Subgroup.normalClosure (c : Set G)=S := by
    apply le_antisymm (Subgroup.normalClosure_le_normal hcS)
    simpa only [sup_bot_eq] using hcStep
  exact (MarkedC4.normalGen_le hcS hcClosure).trans (hcCard.trans_eq hcard)

end SymmetricSubgroupAsymptotics
