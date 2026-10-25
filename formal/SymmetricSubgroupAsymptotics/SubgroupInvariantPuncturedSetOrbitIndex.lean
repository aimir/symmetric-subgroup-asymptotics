import SymmetricSubgroupAsymptotics.SubgroupInvariantSetOrbitIndex
import Mathlib.Data.Set.Card

/-! A fixed point can be deleted from an invariant set before counting
the SAME subgroup orbit. This is purely a finite group-action lemma. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SubgroupInvariantPuncturedSetOrbitIndex

theorem orbit_card_le_invariant_set_sub_one_mul_index
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (L : Subgroup G) (S : Set X) (z x : X) (hz : z ∈ S) (hx : x ∈ S)
    (hne : x ≠ z) (hfix : ∀ g : G, g • z=z)
    (hS : ∀ g : L, ∀ y ∈ S, g • y ∈ S) :
    Nat.card (MulAction.orbit G x) ≤ (Nat.card S-1)*L.index := by
  have hx' : x ∈ S \ {z} := ⟨hx,by simpa only [Set.mem_singleton_iff] using hne⟩
  have hS' : ∀ g : L, ∀ y ∈ S \ {z}, g • y ∈ S \ {z} := by
    intro g y hy
    refine ⟨hS g y hy.1,?_⟩
    intro hh
    have he : (g : G) • y=z := Set.mem_singleton_iff.mp hh
    have hyz : y=z := (MulAction.injective (g : G)) (he.trans (hfix g.val).symm)
    exact hy.2 (Set.mem_singleton_iff.mpr hyz)
  have hh := SubgroupInvariantSetOrbitIndex.orbit_card_le_invariant_set_mul_index
    L (S \ {z}) x hx' hS'
  have hc : Nat.card (S \ ({z} : Set X) : Set X)=Nat.card S-1 :=
    Set.ncard_diff_singleton_of_mem hz
  rw [hc] at hh
  exact hh

end SymmetricSubgroupAsymptotics.SubgroupInvariantPuncturedSetOrbitIndex
