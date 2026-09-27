import SymmetricSubgroupAsymptotics.OrbitProfileFromOrbits
import SymmetricSubgroupAsymptotics.CriticalActionModels

/-! The unique original singleton and pair actions, identified through
actual point charts. The pair proof uses transitivity and the two-element
permutation group, not an abstract-group replacement or a catalogue. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SmallOriginalOrbitCharts

theorem transitive_eq_top_of_card_two {Y : Type*} [Fintype Y]
    (V : Subgroup (Equiv.Perm Y)) (hcard : Nat.card Y = 2)
    (htrans : ∀ x y : Y, ∃ v : V, (v : Equiv.Perm Y) x = y) : V = ⊤ := by
  have hc : Fintype.card Y = 2 := by rwa [← Nat.card_eq_fintype_card]
  letI : Nonempty Y := Fintype.card_pos_iff.mp (by omega)
  let x : Y := Classical.choice inferInstance
  have hs : Function.Surjective (fun v : V => (v : Equiv.Perm Y) x) := htrans x
  have hlow : Nat.card Y ≤ Nat.card V := Nat.card_le_card_of_surjective _ hs
  have hp : Nat.card (Equiv.Perm Y) = 2 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,hc]
    norm_num
  apply V.eq_top_of_le_card
  rw [hp]
  simpa only [hcard] using hlow

theorem critical_pair_eq_top : criticalActionSubgroup .c2 = ⊤ := by
  apply (criticalActionSubgroup .c2).eq_top_of_card_eq
  rw [criticalAction_group_card,Nat.card_eq_fintype_card,Fintype.card_perm,
    criticalAction_point_card]
  norm_num [criticalActionOrder,criticalActionDegree]

variable {X : Type} [Fintype X] (H : Subgroup (Equiv.Perm X))
    (o : OrbitProfileFromOrbits.Orbit H)

theorem singleton_chart (hcard : Nat.card o.orbit = 1) :
    ∃ e : PUnit.{1} ≃ o.orbit,
      relabelSubgroup e (⊤ : Subgroup (Equiv.Perm PUnit.{1})) =
        OrbitProfileFromOrbits.orbitImage H o := by
  letI : Fintype o.orbit := Fintype.ofFinite _
  have hc : Fintype.card o.orbit = 1 := by rwa [← Nat.card_eq_fintype_card]
  let e : PUnit.{1} ≃ o.orbit := Fintype.equivOfCardEq (by simpa using hc.symm)
  have he : relabelSubgroup e.symm (OrbitProfileFromOrbits.orbitImage H o) =
      (⊤ : Subgroup (Equiv.Perm PUnit.{1})) := Subsingleton.elim _ _
  refine ⟨e,?_⟩
  rw [← he]
  exact relabelSubgroup_symm e.symm (OrbitProfileFromOrbits.orbitImage H o)

theorem pair_chart (hcard : Nat.card o.orbit = 2) :
    ∃ e : criticalActionPoints .c2 ≃ o.orbit,
      relabelSubgroup e (criticalActionSubgroup .c2) =
        OrbitProfileFromOrbits.orbitImage H o := by
  letI : Fintype o.orbit := Fintype.ofFinite _
  have hc : Fintype.card o.orbit = 2 := by rwa [← Nat.card_eq_fintype_card]
  let e : criticalActionPoints .c2 ≃ o.orbit :=
    Fintype.equivOfCardEq ((criticalAction_point_card .c2).trans hc.symm)
  have htrans : ∀ x y : o.orbit, ∃ v : OrbitProfileFromOrbits.orbitImage H o,
      (v : Equiv.Perm o.orbit) x = y := by
    intro x y
    obtain ⟨h,hh⟩ := MulAction.exists_smul_eq H x y
    exact ⟨⟨MulAction.toPermHom H o.orbit h,⟨h,rfl⟩⟩,hh⟩
  have hi := transitive_eq_top_of_card_two (OrbitProfileFromOrbits.orbitImage H o)
    hcard htrans
  refine ⟨e,?_⟩
  rw [critical_pair_eq_top,hi]
  exact (relabelSubgroup e).map_top

end SymmetricSubgroupAsymptotics.SmallOriginalOrbitCharts

end
