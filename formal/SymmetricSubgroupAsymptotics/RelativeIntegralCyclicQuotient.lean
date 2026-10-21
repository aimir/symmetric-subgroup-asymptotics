import SymmetricSubgroupAsymptotics.RelativeIntegralAbelianSupplement
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! A cyclic actual quotient supplies an actual cyclic supplement. The
full relative coinvariant order is then exactly the abelianization order
divided by the actual subgroup index. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G : Type} [Group G] (E : Subgroup G) [E.Normal] [IsCyclic (G ⧸ E)]

private theorem exists_cyclic_supplement : ∃ g : G, E ⊔ Subgroup.zpowers g = ⊤ := by
  let q := QuotientGroup.mk' E
  obtain ⟨x, hx⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic (G ⧸ E))
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective E x
  refine ⟨g, ?_⟩
  have hemap : E.map q = ⊥ := by
    ext z
    constructor
    · rintro ⟨e, he, rfl⟩
      exact (QuotientGroup.eq_one_iff e).mpr he
    · intro hz
      rw [Subgroup.mem_bot] at hz
      subst z
      exact Subgroup.one_mem _
  have hm : (E ⊔ Subgroup.zpowers g).map q = ⊤ := by
    rw [Subgroup.map_sup, hemap, bot_sup_eq, MonoidHom.map_zpowers, hx]
  have h := congrArg (Subgroup.comap q) hm
  rw [Subgroup.comap_map_eq, Subgroup.comap_top] at h
  have hker : q.ker = E := QuotientGroup.ker_mk' E
  rw [hker] at h
  have habs : (E ⊔ Subgroup.zpowers g) ⊔ E = E ⊔ Subgroup.zpowers g :=
    sup_eq_left.mpr le_sup_left
  rw [habs] at h
  exact h

theorem relative_commutator_eq_derived_of_cyclic_quotient :
    ⁅E, (⊤ : Subgroup G)⁆ = commutator G := by
  obtain ⟨g, hg⟩ := exists_cyclic_supplement E
  exact relative_commutator_eq_derived_of_abelian_supplement E (Subgroup.zpowers g) hg

theorem relative_integral_order_mul_index_of_cyclic_quotient [Finite G] :
    (⁅E, (⊤ : Subgroup G)⁆).relIndex E * E.index = Nat.card (Abelianization G) := by
  obtain ⟨g, hg⟩ := exists_cyclic_supplement E
  exact relative_integral_order_mul_index_of_abelian_supplement E (Subgroup.zpowers g) hg

/-- In particular an actual index-two normal loses a whole integral bit. -/
theorem relative_integral_order_le_sixteen_of_cyclic_quotient [Finite G]
    (hAb : Nat.card (Abelianization G) ≤ 32) (hindex : 2 ≤ E.index) :
    (⁅E, (⊤ : Subgroup G)⁆).relIndex E ≤ 16 := by
  have h := relative_integral_order_mul_index_of_cyclic_quotient E
  have hm : (⁅E, (⊤ : Subgroup G)⁆).relIndex E * 2 ≤ 32 :=
    (Nat.mul_le_mul_left _ hindex).trans (h.le.trans hAb)
  omega

end SymmetricSubgroupAsymptotics
