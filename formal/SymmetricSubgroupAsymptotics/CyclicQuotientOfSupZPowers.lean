import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Cyclic quotients displayed by one ambient element -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- If a normal subgroup together with one cyclic subgroup generates the
ambient group, then the quotient by that normal subgroup is cyclic. -/
theorem isCyclic_quotient_of_sup_zpowers_eq_top
    {G : Type} [Group G]
    (B : Subgroup G) [B.Normal] (z : G)
    (hgen : B ⊔ Subgroup.zpowers z = ⊤) :
    IsCyclic (G ⧸ B) := by
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨QuotientGroup.mk' B z, ?_⟩
  have hmap := congrArg
    (fun H : Subgroup G ↦ H.map (QuotientGroup.mk' B)) hgen
  change Subgroup.map (QuotientGroup.mk' B)
      (B ⊔ Subgroup.zpowers z) =
    Subgroup.map (QuotientGroup.mk' B) ⊤ at hmap
  have hB : Subgroup.map (QuotientGroup.mk' B) B = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have htop : Subgroup.map (QuotientGroup.mk' B) ⊤ = ⊤ := by
    exact Subgroup.map_top_of_surjective (QuotientGroup.mk' B)
      (QuotientGroup.mk'_surjective B)
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, hB, htop, bot_sup_eq] at hmap
  exact hmap

end SymmetricSubgroupAsymptotics

end
