import SymmetricSubgroupAsymptotics.RepeatedMarkerOwnerBound

/-!
# The first non-2 outside orbit

An outside orbit of degree three has a transitive proper image in `S₃`.
The only such literal permutation subgroup is `A₃`.  Thus the degree-three
part of the remaining ordinary family is exactly the natural cyclic marker;
every other outside orbit has degree at least four.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerOwnerBound

/-- Structural classification on the literal three-point set.  Transitivity
injects the three points into the subgroup.  Lagrange and properness force
order three, after which the sign of every element is trivial. -/
private theorem transitive_proper_degreeThree_eq_alternating :
    ∀ A : Subgroup (Equiv.Perm (Fin 3)),
      PermutationSubgroupTransitive A → A ≠ ⊤ →
        A = alternatingGroup (Fin 3) := by
  intro A htrans hproper
  let liftPoint : Fin 3 → A := fun y =>
    ⟨Classical.choose (htrans 0 y), (Classical.choose_spec (htrans 0 y)).1⟩
  have hlift : Function.Injective liftPoint := by
    intro y z hyz
    have hy := (Classical.choose_spec (htrans 0 y)).2
    have hz := (Classical.choose_spec (htrans 0 z)).2
    have hperm : Classical.choose (htrans 0 y) =
        Classical.choose (htrans 0 z) := congrArg Subtype.val hyz
    rw [hperm] at hy
    exact hy.symm.trans hz
  have hlower : 3 ≤ Nat.card A := by
    simpa using Nat.card_le_card_of_injective liftPoint hlift
  have hupper : Nat.card A < 6 := by
    have hle : Nat.card A ≤ Nat.card (Equiv.Perm (Fin 3)) :=
      Subgroup.card_le_card_group A
    have hne : Nat.card A ≠ Nat.card (Equiv.Perm (Fin 3)) := by
      intro hcard
      exact hproper (Subgroup.eq_top_of_card_eq A hcard)
    have hperm : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
    omega
  have hdiv : Nat.card A ∣ 6 := by
    have h := Subgroup.card_subgroup_dvd_card A
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm] at h ⊢
    exact h
  have hcardA : Nat.card A = 3 := by
    interval_cases h : Nat.card A
    · rfl
    · norm_num [h] at hdiv
    · norm_num [h] at hdiv
  have hle : A ≤ alternatingGroup (Fin 3) := by
    intro g hg
    rw [Equiv.Perm.mem_alternatingGroup]
    have hpowA := pow_card_eq_one' (x := (⟨g,hg⟩ : A))
    rw [hcardA] at hpowA
    have hpow : g ^ 3 = 1 := congrArg Subtype.val hpowA
    have hsignpow : Equiv.Perm.sign g ^ 3 = 1 := by
      rw [← map_pow,hpow,map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hsign | hsign
    · exact hsign
    · rw [hsign] at hsignpow
      norm_num at hsignpow
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [nat_card_alternatingGroup,hcardA]
  norm_num [Nat.card_eq_fintype_card]

/-- A degree-three outside orbit is the natural cyclic `C₃ = A₃` action,
with an explicit relabelling of the original orbit. -/
theorem outsideOrbit_degree_three_chart {X : Type} [Fintype X]
    (H : Subgroup (Equiv.Perm X)) (o : OutsideOrbit H)
    (hcard : Nat.card o.1.orbit = 3) :
    ∃ e : Fin 3 ≃ o.1.orbit,
      relabelSubgroup e (alternatingGroup (Fin 3)) =
        OrbitProfileFromOrbits.orbitImage H o.1 := by
  letI : Fintype o.1.orbit := Fintype.ofFinite _
  have hc : Fintype.card o.1.orbit = 3 := by
    rwa [← Nat.card_eq_fintype_card]
  let e : Fin 3 ≃ o.1.orbit := Fintype.equivOfCardEq (by simpa using hc.symm)
  let A : Subgroup (Equiv.Perm (Fin 3)) :=
    relabelSubgroup e.symm (OrbitProfileFromOrbits.orbitImage H o.1)
  have horbit : ∀ x y : o.1.orbit,
      ∃ v : OrbitProfileFromOrbits.orbitImage H o.1,
        (v : Equiv.Perm o.1.orbit) x = y := by
    intro x y
    obtain ⟨h,hh⟩ := MulAction.exists_smul_eq H x y
    exact ⟨⟨MulAction.toPermHom H o.1.orbit h,⟨h,rfl⟩⟩,hh⟩
  have htrans : PermutationSubgroupTransitive A := by
    intro x y
    obtain ⟨v,hv⟩ := horbit (e x) (e y)
    refine ⟨e.symm.permCongr v, ?_, ?_⟩
    · dsimp [A]
      rw [mem_relabelSubgroup]
      have heq : e.symm.symm.permCongr
          (e.symm.permCongr (v : Equiv.Perm o.1.orbit)) = v :=
        (e.symm.permCongr).symm_apply_apply v
      rw [heq]
      exact v.property
    · change e.symm ((v : Equiv.Perm o.1.orbit) (e x)) = y
      rw [hv,e.symm_apply_apply]
  have hproper : A ≠ ⊤ := by
    intro htop
    apply o.2.2
    refine ⟨e, ?_⟩
    calc
      relabelSubgroup e oddMarkerActionSubgroup = relabelSubgroup e A := by
        simp [oddMarkerActionSubgroup,htop]
      _ = OrbitProfileFromOrbits.orbitImage H o.1 :=
        relabelSubgroup_symm e.symm _
  have hA : A = alternatingGroup (Fin 3) :=
    transitive_proper_degreeThree_eq_alternating A htrans hproper
  refine ⟨e, ?_⟩
  calc
    relabelSubgroup e (alternatingGroup (Fin 3)) = relabelSubgroup e A := by rw [hA]
    _ = OrbitProfileFromOrbits.orbitImage H o.1 := relabelSubgroup_symm e.symm _

/-- Exact split at the first non-2 frontier: the outside orbit is the natural
cyclic degree-three action, or its original degree is at least four. -/
theorem outsideOrbit_c3_or_card_ge_four {X : Type} [Fintype X]
    (H : Subgroup (Equiv.Perm X)) (o : OutsideOrbit H) :
    (∃ e : Fin 3 ≃ o.1.orbit,
      relabelSubgroup e (alternatingGroup (Fin 3)) =
        OrbitProfileFromOrbits.orbitImage H o.1) ∨
      4 ≤ Nat.card o.1.orbit := by
  by_cases hcard : Nat.card o.1.orbit = 3
  · exact Or.inl (outsideOrbit_degree_three_chart H o hcard)
  · right
    have hgt := outsideOrbit_card_gt_two H o
    omega

end SymmetricSubgroupAsymptotics.RepeatedMarkerOwnerBound

end
