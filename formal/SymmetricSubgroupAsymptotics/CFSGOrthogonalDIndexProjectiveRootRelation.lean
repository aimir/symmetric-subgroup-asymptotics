import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootElements

/-! Arbitrary automorphisms of the SAME original projective D group
preserve its intrinsic commuting/root-product relation on actual root
subgroups. This supplies relation preservation separately from any
point reconstruction, semilinear classification, or D4 triality claim. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootAdjacency
open CFSGOrthogonalDSerreMatrices
variable (K : Type) [Field K]

def RootProductRelation (s : ℕ) (L M : Subgroup (elementaryProjective K (s + 4))) : Prop :=
  ∃ x ∈ L, x ≠ 1 ∧ ∃ y ∈ M, y ≠ 1 ∧ Commute x y ∧ IsProjectiveRootElement K s (x * y)

theorem automorphism_maps_RootProductRelation [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
    (f : MulAut (elementaryProjective K (s + 4)))
    (L M : Subgroup (elementaryProjective K (s + 4)))
    (h : RootProductRelation K s L M) :
    RootProductRelation K s (L.map f.toMonoidHom) (M.map f.toMonoidHom) := by
  obtain ⟨x, hx, hxn, y, hy, hyn, hc, hp⟩ := h
  refine ⟨f x, ⟨x, hx, rfl⟩, ?_, f y, ⟨y, hy, rfl⟩, ?_, ?_, ?_⟩
  · intro he
    exact hxn (f.injective (he.trans f.map_one.symm))
  · intro he
    exact hyn (f.injective (he.trans f.map_one.symm))
  · change f x * f y = f y * f x
    simpa only [map_mul] using congrArg f hc.eq
  · simpa only [map_mul] using automorphism_isProjectiveRootElement K p s f (x * y) hp

private theorem map_symm_map (s : ℕ) (f : MulAut (elementaryProjective K (s + 4)))
    (L : Subgroup (elementaryProjective K (s + 4))) :
    (L.map f.toMonoidHom).map f.symm.toMonoidHom = L := by
  have he : f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    exact f.symm_apply_apply x
  rw [Subgroup.map_map, he, Subgroup.map_id]

theorem automorphism_RootProductRelation_iff [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
    (f : MulAut (elementaryProjective K (s + 4)))
    (L M : Subgroup (elementaryProjective K (s + 4))) :
    RootProductRelation K s (L.map f.toMonoidHom) (M.map f.toMonoidHom) ↔
      RootProductRelation K s L M := by
  constructor
  · intro h
    have hh := automorphism_maps_RootProductRelation K p s f.symm _ _ h
    rw [map_symm_map K s f L, map_symm_map K s f M] at hh
    exact hh
  · exact automorphism_maps_RootProductRelation K p s f L M

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootAdjacency
