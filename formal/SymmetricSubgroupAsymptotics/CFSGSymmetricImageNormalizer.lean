import SymmetricSubgroupAsymptotics.CFSGSymmetricSylowSelfNormalizer

/-! A subgroup mapping onto a symmetric Sylow two-subgroup through a
map with two-group kernel has a two-group normalizer. The actual action
image, rather than a guessed ambient Sylow identity, is sufficient. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymmetricImageNormalizer
open Equiv

theorem normalizer_isPGroup {G X : Type*} [Group G] [Fintype X] [DecidableEq X]
    (H : Subgroup G) (f : G →* Perm X) (hker : IsPGroup 2 f.ker)
    (Q : Sylow 2 (Perm X)) (himage : H.map f = (Q : Subgroup (Perm X))) :
    IsPGroup 2 (Subgroup.normalizer (H : Set G)) := by
  have hle : Subgroup.normalizer (H : Set G) ≤ (Q : Subgroup (Perm X)).comap f := by
    rw [← Subgroup.map_le_iff_le_comap]
    have hn := Subgroup.le_normalizer_map (H := H) f
    rw [himage] at hn
    change (Subgroup.normalizer (H : Set G)).map f ≤
      Subgroup.normalizer (Q : Set (Perm X)) at hn
    rw [CFSGSymmetricSylowSelfNormalizer.normalizer_eq_self Q] at hn
    exact hn
  exact (Q.isPGroup'.comap_of_ker_isPGroup f hker).to_le hle

end SymmetricSubgroupAsymptotics.CFSGSymmetricImageNormalizer
