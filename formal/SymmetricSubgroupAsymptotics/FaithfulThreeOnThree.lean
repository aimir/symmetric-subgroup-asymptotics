import SymmetricSubgroupAsymptotics.OrbitProfileAssembly
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# A faithful action of a three-group on three points

The local coefficient in Tracey's binary rank-two formula is an orbit
count on the three nonzero dual vectors.  This file isolates the elementary
finite permutation fact used there: a group of order three acting faithfully
on a set of order three acts transitively.  The proof identifies the literal
permutation image with `A₃`; no classification input is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

private theorem orderThree_subgroup_perm_finThree_eq_alternating
    (T : Subgroup (Equiv.Perm (Fin 3)))
    (hT : Nat.card T = 3) :
    T = alternatingGroup (Fin 3) := by
  have hle : T ≤ alternatingGroup (Fin 3) := by
    intro g hg
    rw [Equiv.Perm.mem_alternatingGroup]
    have hpowT := pow_card_eq_one' (x := (⟨g, hg⟩ : T))
    rw [hT] at hpowT
    have hpow : g ^ 3 = 1 := congrArg Subtype.val hpowT
    have hsignpow : Equiv.Perm.sign g ^ 3 = 1 := by
      rw [← map_pow, hpow, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hsign | hsign
    · exact hsign
    · rw [hsign] at hsignpow
      norm_num at hsignpow
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [nat_card_alternatingGroup, hT]
  norm_num [Nat.card_eq_fintype_card]

/-- A faithful action of a finite group of order three on a finite set of
order three is transitive. -/
theorem faithful_three_on_three_isPretransitive
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X]
    (hG : Nat.card G = 3) (hX : Nat.card X = 3) :
    MulAction.IsPretransitive G X := by
  letI : Fintype X := Fintype.ofFinite X
  let e : X ≃ Fin 3 := Fintype.equivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hX)
  let tau : G →* Equiv.Perm (Fin 3) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G X)
  have htau : Function.Injective tau := by
    intro g h hgh
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro x
    have hgh' : MulAction.toPermHom G X g =
        MulAction.toPermHom G X h :=
      e.permCongrHom.injective (by simpa [tau] using hgh)
    exact DFunLike.congr_fun hgh' x
  let T : Subgroup (Equiv.Perm (Fin 3)) := tau.range
  have hTcard : Nat.card T = 3 := by
    let equiv : G ≃ T :=
      (MulEquiv.ofBijective tau.rangeRestrict
        ⟨MonoidHom.rangeRestrict_injective_iff.mpr htau,
          tau.rangeRestrict_surjective⟩).toEquiv
    calc
      Nat.card T = Nat.card G := (Nat.card_congr equiv).symm
      _ = 3 := hG
  have hT : T = alternatingGroup (Fin 3) :=
    orderThree_subgroup_perm_finThree_eq_alternating T hTcard
  apply MulAction.IsPretransitive.mk
  intro x y
  letI : MulAction.IsPretransitive (alternatingGroup (Fin 3)) (Fin 3) :=
    alternatingGroup.isPretransitive_of_three_le_card (Fin 3) (by norm_num)
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq
    (alternatingGroup (Fin 3)) (e x) (e y)
  have haT : (a.1 : Equiv.Perm (Fin 3)) ∈ T := by
    rw [hT]
    exact a.2
  obtain ⟨g, hg⟩ := haT
  refine ⟨g, e.injective ?_⟩
  change e (g • x) = e y
  calc
    e (g • x) = tau g (e x) := by simp [tau]
    _ = a.1 (e x) := by rw [hg]
    _ = e y := ha

/-- Consequently the orbit quotient of that action has one element. -/
theorem faithful_three_on_three_orbitQuotient_card
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X]
    (hG : Nat.card G = 3) (hX : Nat.card X = 3) :
    Nat.card (MulAction.orbitRel.Quotient G X) = 1 := by
  letI : MulAction.IsPretransitive G X :=
    faithful_three_on_three_isPretransitive G X hG hX
  letI : Nonempty X :=
    (Nat.card_pos_iff.mp (by rw [hX]; norm_num)).1
  obtain huniq : Nonempty (Unique (MulAction.orbitRel.Quotient G X)) :=
    (MulAction.pretransitive_iff_unique_quotient_of_nonempty G X).mp
      inferInstance
  letI := Classical.choice huniq
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

end SymmetricSubgroupAsymptotics

end
