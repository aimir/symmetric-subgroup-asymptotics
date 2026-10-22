import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyAction
import SymmetricSubgroupAsymptotics.CFSGInnerActionFaithfulness

/-! A subgroup of actual automorphisms containing all inner automorphisms
acts faithfully on a stable injectively labelled proper subgroup family
of a simple group. Full automorphism invariance is not required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyActionFaithfulness
open CFSGSubgroupFamilyAction
variable {G X : Type*} [Group G] [IsSimpleGroup G]

theorem permutationHom_injective (S : Subgroup (MulAut G))
    (hinner : ∀ g : G, MulAut.conj g ∈ S)
    (L : X → Subgroup G) (hinj : Function.Injective L)
    (hstable : ∀ a : S, ∀ x, ∃ y, L y = (L x).map a.val.toMonoidHom)
    (x₀ : X) (hne : L x₀ ≠ ⊥) (hproper : L x₀ ≠ ⊤) :
    Function.Injective (permutationHom S.subtype L hinj hstable) := by
  let pi := permutationHom S.subtype L hinj hstable
  let inner : G →* S := (MulAut.conj : G →* MulAut G).codRestrict S hinner
  have hi : Function.Injective (pi.comp inner) := by
    rcases (inferInstance : (pi.comp inner).ker.Normal).eq_bot_or_eq_top with hb | ht
    · exact (pi.comp inner).ker_eq_bot_iff.mp hb
    · apply False.elim
      have hall (g : G) : pi (inner g) = 1 := by
        have hg : g ∈ (pi.comp inner).ker := by rw [ht]; trivial
        exact MonoidHom.mem_ker.mp hg
      have hmap (g : G) : (L x₀).map (MulAut.conj g).toMonoidHom = L x₀ := by
        have h := label_permutation S.subtype L hinj hstable (inner g) x₀
        change L (pi (inner g) x₀) = (L x₀).map (MulAut.conj g).toMonoidHom at h
        rw [hall] at h
        exact h.symm
      letI : (L x₀).Normal := ⟨by
        intro n hn g
        change MulAut.conj g n ∈ L x₀
        rw [← hmap g]
        exact ⟨n, hn, rfl⟩⟩
      rcases (inferInstance : (L x₀).Normal).eq_bot_or_eq_top with hb | ht
      · exact hne hb
      · exact hproper ht
  intro a b hab
  change pi a = pi b at hab
  apply Subtype.ext
  ext g
  apply hi
  have hconj (a : S) : inner (a.val g) = a * inner g * a⁻¹ := by
    apply Subtype.ext
    exact CFSGInnerActionFaithfulness.conj_automorphism a.val g
  change pi (inner (a.val g)) = pi (inner (b.val g))
  simp only [hconj, map_mul, map_inv, hab]

end SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyActionFaithfulness
