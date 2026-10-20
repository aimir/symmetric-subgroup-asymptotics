import SymmetricSubgroupAsymptotics.FiniteGroupPowerGeneratorBound
import Mathlib.GroupTheory.QuotientGroup.Finite

/-! An actual ordinary generating set in a quotient lifts with the same
cardinality to a supplement of its original kernel. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

theorem lift_generating_finset_mod_kernel
    {G Q : Type} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (S : Finset Q)
    (hS : Subgroup.closure (S : Set Q)=⊤) :
    ∃ T : Finset G, T.card≤S.card ∧ Subgroup.closure (T : Set G)⊔f.ker=⊤ := by
  let lift : Q → G := fun q => Classical.choose (hf q)
  have hlift : ∀ q, f (lift q)=q := fun q => Classical.choose_spec (hf q)
  let T : Finset G := S.image lift
  let H : Subgroup G := Subgroup.closure (T : Set G)
  have hmap : H.map f=⊤ := by
    apply top_unique
    rw [←hS]
    apply (Subgroup.closure_le (H.map f)).mpr
    intro q hq
    exact ⟨lift q,Subgroup.subset_closure (Finset.mem_image.mpr ⟨q,hq,rfl⟩),hlift q⟩
  refine ⟨T,Finset.card_image_le,top_unique ?_⟩
  intro g _
  have hm : f g∈H.map f := by rw [hmap]; trivial
  obtain ⟨x,hx,hxg⟩ := hm
  have hk : x⁻¹*g∈f.ker := by
    change f (x⁻¹*g)=1
    rw [map_mul,map_inv,hxg,inv_mul_cancel]
  have h := (H⊔f.ker).mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hk)
  simpa only [mul_inv_cancel_left] using h

theorem exists_generating_supplement_of_quotient_card_le_pow
    {G : Type} [Group G] [Finite G] (C : Subgroup G) [C.Normal] (d a : ℕ)
    (hcard : Nat.card (G⧸C)≤d^a) :
    ∃ T : Finset G, T.card≤d*a ∧ Subgroup.closure (T : Set G)⊔C=⊤ := by
  obtain ⟨S,hS,hsize⟩ := MarkedC4.exists_generating_finset_card_le_of_card_le_pow
    (G⧸C) d a hcard
  obtain ⟨T,hT,hgen⟩ := lift_generating_finset_mod_kernel
    (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C) S hS
  refine ⟨T,hT.trans hsize,?_⟩
  simpa only [QuotientGroup.ker_mk'] using hgen

end SymmetricSubgroupAsymptotics
