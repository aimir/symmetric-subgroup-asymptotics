import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyPermutation
import SymmetricSubgroupAsymptotics.CFSGInnerActionFaithfulness

/-! A nontrivial proper subgroup of a simple group makes every stable,
injectively labelled subgroup family a faithful automorphism geometry.
The original labels and their literal subgroup maps are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyFaithfulness
open CFSGSubgroupFamilyPermutation
variable {G X : Type*} [Group G] [IsSimpleGroup G]

theorem permutationHom_injective (L : X → Subgroup G) (hinj : Function.Injective L)
    (hstable : ∀ a : MulAut G, ∀ x, ∃ y, L y = (L x).map a.toMonoidHom)
    (x₀ : X) (hne : L x₀ ≠ ⊥) (hproper : L x₀ ≠ ⊤) :
    Function.Injective (permutationHom L hinj hstable) := by
  apply CFSGInnerActionFaithfulness.injective_of_inner_nontrivial
  by_contra h
  have hall : ∀ g : G, permutationHom L hinj hstable (MulAut.conj g) = 1 := by
    simpa only [not_exists, not_not] using h
  have hmap (g : G) : (L x₀).map (MulAut.conj g).toMonoidHom = L x₀ := by
    have he := label_permutation L hinj hstable (MulAut.conj g) x₀
    rw [hall] at he
    exact he.symm
  letI hnormal : (L x₀).Normal := ⟨by
    intro n hn g
    change MulAut.conj g n ∈ L x₀
    rw [← hmap g]
    exact ⟨n, hn, rfl⟩⟩
  rcases hnormal.eq_bot_or_eq_top with hb | ht
  · exact hne hb
  · exact hproper ht

end SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyFaithfulness
