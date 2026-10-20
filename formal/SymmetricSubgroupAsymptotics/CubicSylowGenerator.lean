import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Choose an actual nonidentity cubic generator of an actual Sylow
subgroup of cardinal three; its literal subgroup is retained. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CubicSylowGenerator

theorem exists_generator {G : Type} [Group G] [Finite G]
    (S : Sylow 3 G) (hcard : Nat.card S = 3) :
    ∃ s : G, (S : Subgroup G) = Subgroup.zpowers s ∧ s^3 = 1 ∧ s ≠ 1 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : IsCyclic S := isCyclic_of_prime_card hcard
  obtain ⟨z,hz⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic S)
  have ho : orderOf z = 3 := (orderOf_eq_card_of_zpowers_eq_top hz).trans hcard
  have hcube : z^3 = 1 := by
    simpa only [ho] using pow_orderOf_eq_one z
  have hne : z ≠ 1 := by
    intro h
    rw [h,orderOf_one] at ho
    exact (by decide : (1 : ℕ) ≠ 3) ho
  have hm := congrArg (fun K : Subgroup S => K.map (S : Subgroup G).subtype) hz
  change (Subgroup.zpowers z).map (S : Subgroup G).subtype =
    (⊤ : Subgroup S).map (S : Subgroup G).subtype at hm
  rw [MonoidHom.map_zpowers,← MonoidHom.range_eq_map,Subgroup.range_subtype] at hm
  refine ⟨z.1,hm.symm,congrArg Subtype.val hcube,?_⟩
  intro h
  exact hne (Subtype.ext h)

end SymmetricSubgroupAsymptotics.CubicSylowGenerator
