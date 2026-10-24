import Mathlib.GroupTheory.Index

/-! Exact cardinal factorization for a subgroup and the kernel and image of
one homomorphism. The kernel is parameterized by an actual injective map;
the subgroup is kept fixed throughout. Surjectivity onto the ambient target
is not required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.ExactHomSubgroupCardinality

variable {G V Z : Type*} [Group G] [Group V] [Group Z]

def kernelIntersectionEquiv (f : G →* V) (ι : Z →* G)
    (hι : Function.Injective ι) (hexact : ι.range = f.ker) (L : Subgroup G) :
    (L.comap ι) ≃ (f.ker.subgroupOf L) :=
  Equiv.ofBijective
    (fun z => ⟨⟨ι z.val, z.property⟩, by
      change ι z.val ∈ f.ker
      rw [← hexact]
      exact ⟨z.val, rfl⟩⟩)
    ⟨by
      intro x y hxy
      apply Subtype.ext
      apply hι
      exact congrArg (fun z : f.ker.subgroupOf L => z.val.val) hxy,
    by
      intro x
      have hx : x.val.val ∈ ι.range := by rw [hexact]; exact x.property
      obtain ⟨z, hz⟩ := hx
      refine ⟨⟨z, ?_⟩, ?_⟩
      · change ι z ∈ L
        rw [hz]
        exact x.val.property
      · apply Subtype.ext
        exact Subtype.ext hz⟩

theorem card_comap_mul_card_map [Finite G]
    (f : G →* V) (ι : Z →* G) (hι : Function.Injective ι)
    (hexact : ι.range = f.ker) (L : Subgroup G) :
    Nat.card (L.comap ι) * Nat.card (L.map f) = Nat.card L := by
  have hc := (f.ker.subgroupOf L).card_mul_index
  have hi : (f.ker.subgroupOf L).index = Nat.card (L.map f) :=
    Subgroup.relIndex_ker L f
  rw [hi] at hc
  rw [Nat.card_congr (kernelIntersectionEquiv f ι hι hexact L)]
  exact hc

end SymmetricSubgroupAsymptotics.ExactHomSubgroupCardinality
