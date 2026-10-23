import SymmetricSubgroupAsymptotics.CFSGFourRootPathPermutation
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Commute.Hom

/-! An actual subgroup permutation preserves a commutation graph.
Specializing to the four-node path bounds its possible permutations by
identity and reversal, without orienting the root lengths. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSubgroupCommutationPermutation
open CFSGFourRootPathPermutation

def SubgroupsCommute {G : Type*} [Group G] (R S : Subgroup G) : Prop :=
  ∀ x ∈ R, ∀ y ∈ S, Commute x y

theorem ranges_commute_iff {G A B : Type*} [Group G] [Group A] [Group B]
    (u : A →* G) (v : B →* G) :
    SubgroupsCommute u.range v.range ↔ ∀ a b, Commute (u a) (v b) := by
  constructor
  · intro h a b
    exact h _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
  · intro h
    rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
    exact h a b

theorem map_equiv_iff {G : Type*} [Group G] (f : MulAut G) (R S : Subgroup G) :
    SubgroupsCommute (R.map f.toMonoidHom) (S.map f.toMonoidHom) ↔ SubgroupsCommute R S := by
  constructor
  · intro h x hx y hy
    have hh := h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    apply f.injective
    simpa only [map_mul] using hh.eq
  · intro h
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact (h x hx y hy).map f.toMonoidHom

theorem path_preserved {G : Type*} [Group G] (R : Fin 4 → Subgroup G)
    (hgraph : ∀ i j, SubgroupsCommute (R i) (R j) ↔ ¬ adjacent i j)
    (f : MulAut G) (sigma : Equiv.Perm (Fin 4))
    (hmap : ∀ i, (R i).map f.toMonoidHom = R (sigma i)) : PreservesPath sigma := by
  intro i j
  have hh := map_equiv_iff f (R i) (R j)
  rw [hmap i, hmap j, hgraph, hgraph] at hh
  exact not_iff_not.mp hh

end SymmetricSubgroupAsymptotics.CFSGSubgroupCommutationPermutation
