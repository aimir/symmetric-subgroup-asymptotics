import Mathlib.GroupTheory.QuotientGroup.Basic

/-! A homomorphism retaining an original normal denominator has exact
kernel image in that quotient. No group order or splitting is substituted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.QuotientRetainedHom
variable {G H : Type} [Group G] [Group H]
  (f : G →* H) (N : Subgroup G) [N.Normal] (hN : N≤f.ker)

def descend : G ⧸ N →* H := QuotientGroup.lift N f hN

theorem descend_apply (g : G) : descend f N hN (QuotientGroup.mk' N g)=f g := rfl

theorem descend_surjective (hf : Function.Surjective f) : Function.Surjective (descend f N hN) := by
  intro h
  obtain ⟨g,hg⟩ := hf h
  exact ⟨QuotientGroup.mk' N g,hg⟩

theorem descend_kernel : (descend f N hN).ker=f.ker.map (QuotientGroup.mk' N) := by
  have hc : (descend f N hN).ker.comap (QuotientGroup.mk' N)=f.ker := by
    ext g
    change descend f N hN (QuotientGroup.mk' N g)=1 ↔ f g=1
    rfl
  have hm := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)
    (descend f N hN).ker
  rw [hc] at hm
  exact hm.symm

end SymmetricSubgroupAsymptotics.QuotientRetainedHom
