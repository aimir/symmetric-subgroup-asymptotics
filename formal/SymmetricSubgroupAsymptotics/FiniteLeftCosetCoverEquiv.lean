import SymmetricSubgroupAsymptotics.FiniteLeftCosetCoverComposition

/-! Transport an actual ambient left-coset cover through a group equivalence.
The literal source subgroup and representative coordinates are preserved. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {G G' I K : Type*} [Group G] [Group G']

 theorem leftCoset_covers_equiv_generators (e : G ≃* G')
    (generators : I → G) (representatives : K → G)
    (hcovers : ∀ g : G, ∃ k,
      g * (representatives k)⁻¹ ∈ Subgroup.closure (Set.range generators))
    (g : G') :
    ∃ k, g * (e (representatives k))⁻¹ ∈
      Subgroup.closure (Set.range (fun j => e (generators j))) := by
  obtain ⟨k, hk⟩ := hcovers (e.symm g)
  have hmap : (Subgroup.closure (Set.range generators)).map e.toMonoidHom =
      Subgroup.closure (Set.range (fun j => e (generators j))) := by
    rw [MonoidHom.map_closure]
    apply congrArg Subgroup.closure
    ext x
    constructor
    · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨generators j, ⟨j, rfl⟩, rfl⟩
  have hmem : e (e.symm g * (representatives k)⁻¹) ∈
      (Subgroup.closure (Set.range generators)).map e.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨_, hk, rfl⟩
  rw [hmap] at hmem
  refine ⟨k, ?_⟩
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using hmem

end SymmetricSubgroupAsymptotics
end
