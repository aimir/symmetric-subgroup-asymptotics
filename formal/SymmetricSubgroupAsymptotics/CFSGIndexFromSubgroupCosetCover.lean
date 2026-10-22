import SymmetricSubgroupAsymptotics.CFSGIndexFromCosetCover

/-! A one-sided cover INSIDE an actual ambient subgroup computes its
relative subgroup index. Restriction is proved abstractly, avoiding
reduction of a concrete matrix subgroup's group structure at each
parameter-membership argument. No normality is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGIndexFromSubgroupCosetCover
variable {A G : Type*} [Group A] [Group G] [Finite A]

theorem index_le_of_parameter_subgroup (H L : Subgroup G) (f : A →* G)
    (hf : ∀ a, f a ∈ L) (N : Subgroup A) (hN : ∀ a ∈ N, f a ∈ H)
    (hcover : ∀ g ∈ L, ∃ a, (f a)⁻¹ * g ∈ H) :
    (H.subgroupOf L).index ≤ N.index := by
  let fL : A →* L := f.codRestrict L hf
  have hNL : N ≤ (H.subgroupOf L).comap fL := by
    intro a ha
    exact hN a ha
  have hc : ∀ g : L, ∃ a : A, (fL a)⁻¹ * g ∈ H.subgroupOf L := by
    intro g
    obtain ⟨a, ha⟩ := hcover g.val g.property
    exact ⟨a, ha⟩
  exact CFSGIndexFromCosetCover.index_le_of_parameter_subgroup (H.subgroupOf L) fL N hNL hc

end SymmetricSubgroupAsymptotics.CFSGIndexFromSubgroupCosetCover
