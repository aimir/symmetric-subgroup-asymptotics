import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing

/-! Enlarging the acting ambient group cannot increase the number of
normal generators of an image which is already normal in that group.
The map need not be onto the larger ambient group. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem normal_generating_tuple_map_of_normal_image
    {G H : Type} [Group G] [Group H] (f : G →* H)
    (N : Subgroup G) [(N.map f).Normal] {t : ℕ}
    (x : Fin t → G) (hx : Subgroup.normalClosure (Set.range x) = N) :
    Subgroup.normalClosure (Set.range (fun i => f (x i))) = N.map f := by
  have himage : f '' Set.range x = Set.range (fun i => f (x i)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, Set.mem_range_self i, rfl⟩
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    refine ⟨x i, ?_, rfl⟩
    rw [← hx]
    exact Subgroup.subset_normalClosure (Set.mem_range_self i)
  · rw [← hx, ← himage]
    exact Subgroup.map_normalClosure_le _ f

theorem normalGen_map_le_of_normal_image
    {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (N : Subgroup G) [N.Normal] [(N.map f).Normal] {t : ℕ}
    (hN : MarkedC4.normalGen N ≤ t) : MarkedC4.normalGen (N.map f) ≤ t := by
  obtain ⟨x, hx⟩ := exists_normal_generating_tuple_of_normalGen_le N hN
  exact normalGen_le_of_fin_tuple (fun i => f (x i))
    (normal_generating_tuple_map_of_normal_image f N x hx)

end SymmetricSubgroupAsymptotics

end
