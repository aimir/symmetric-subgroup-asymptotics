import SymmetricSubgroupAsymptotics.NilpotentQuotientSupplement
import Mathlib.Algebra.Group.Subgroup.Finite

/-! A nilpotent-core generating set in an actual quotient lifts to an
ordinary supplement of the original kernel with the same generator budget. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

theorem lift_nilpotent_generating_set_mod_kernel
    {G Q : Type} [Group G] [Finite G] [Group Q] [Finite Q]
    (f : G →* Q) (hf : Function.Surjective f)
    (K : Subgroup Q) [Group.IsNilpotent K] (S : Finset Q)
    (hgen : Subgroup.closure ((S : Set Q)∪K)=⊤) :
    ∃ (H : Subgroup G) (T : Finset G), Group.IsNilpotent H ∧
      T.card ≤ S.card ∧ Subgroup.closure ((T : Set G)∪H)⊔f.ker=⊤ := by
  obtain ⟨H,hH,hmap⟩ := exists_nilpotent_subgroup_map_eq f hf K
  let lift : Q → G := fun q => Classical.choose (hf q)
  have hlift : ∀ q, f (lift q)=q := fun q => Classical.choose_spec (hf q)
  let T : Finset G := S.image lift
  let C : Subgroup G := Subgroup.closure ((T : Set G)∪H)
  have hCmap : C.map f=⊤ := by
    apply top_unique
    rw [←hgen]
    apply (Subgroup.closure_le (C.map f)).mpr
    intro q hq
    rcases hq with hS|hK
    · refine ⟨lift q,Subgroup.subset_closure (Or.inl ?_),hlift q⟩
      exact Finset.mem_image.mpr ⟨q,hS,rfl⟩
    · rw [←hmap] at hK
      obtain ⟨g,hg,hgq⟩ := hK
      exact ⟨g,Subgroup.subset_closure (Or.inr hg),hgq⟩
  refine ⟨H,T,hH,Finset.card_image_le,top_unique ?_⟩
  intro g _
  have hm : f g∈C.map f := by rw [hCmap]; trivial
  obtain ⟨c,hc,hcg⟩ := hm
  have hk : c⁻¹*g∈f.ker := by
    change f (c⁻¹*g)=1
    rw [map_mul,map_inv,hcg,inv_mul_cancel]
  have h := (C⊔f.ker).mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hk)
  simpa only [mul_inv_cancel_left] using h

end SymmetricSubgroupAsymptotics
