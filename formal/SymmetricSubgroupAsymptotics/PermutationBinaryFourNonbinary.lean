import SymmetricSubgroupAsymptotics.PermutationBinaryFourAugmentation
import SymmetricSubgroupAsymptotics.RepresentationElementHead
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# The nonbinary four-point endpoint

A nonbinary transitive permutation image on four points contains a literal
three-cycle.  On the augmentation hyperplane, a three-cycle has a
one-dimensional fixed space.  The element-annihilator head bound therefore
closes the unique degree-four exception left by the exact Tracey formula.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

variable {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    [MulAction.IsPretransitive G X]

/-- A nonbinary transitive permutation image on four points contains an
original element inducing a permutation of order three. -/
theorem exists_order_three_permutation_of_four_nonbinary
    (hcard : Nat.card X = 4)
    (hnon : ¬IsPGroup 2 (MulAction.toPermHom G X).range) :
    ∃ g : G, orderOf (MulAction.toPermHom G X g) = 3 := by
  let Q := (MulAction.toPermHom G X).range
  change ¬IsPGroup 2 Q at hnon
  have hdiv : Nat.card Q ∣ 24 := by
    have h := Subgroup.card_subgroup_dvd_card Q
    have hperm : Nat.card (Equiv.Perm X) = 24 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_eq_nat_card, hcard]
      norm_num
    simpa only [hperm] using h
  have hthree : 3 ∣ Nat.card Q := by
    by_contra hnthree
    have hle : Nat.card Q ≤ 24 := Nat.le_of_dvd (by decide) hdiv
    have hpos : 0 < Nat.card Q := Nat.card_pos
    have hcases : Nat.card Q = 1 ∨ Nat.card Q = 2 ∨
        Nat.card Q = 4 ∨ Nat.card Q = 8 := by
      interval_cases hq : Nat.card Q <;> norm_num [hq] at *
    have hp : IsPGroup 2 Q := by
      rcases hcases with hq | hq | hq | hq
      · exact IsPGroup.of_card (G := Q) (p := 2) (n := 0) (by simpa using hq)
      · exact IsPGroup.of_card (G := Q) (p := 2) (n := 1) (by simpa using hq)
      · exact IsPGroup.of_card (G := Q) (p := 2) (n := 2) (by simpa using hq)
      · exact IsPGroup.of_card (G := Q) (p := 2) (n := 3) (by simpa using hq)
    exact hnon hp
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 3 hthree
  obtain ⟨g, hg⟩ := q.property
  refine ⟨g, ?_⟩
  rw [hg, orderOf_submonoid]
  exact hq

/-- The order-three permutation supplied above is a single three-cycle,
because four is strictly smaller than twice its prime order. -/
theorem isThreeCycle_of_order_three_on_four
    (hcard : Nat.card X = 4) (g : G)
    (hg : orderOf (MulAction.toPermHom G X g) = 3) :
    (MulAction.toPermHom G X g).IsCycle := by
  apply Equiv.Perm.isCycle_of_prime_order'
  · rw [hg]
    decide
  · rw [Fintype.card_eq_nat_card, hcard, hg]
    norm_num

/-- A three-cycle has at most one fixed direction on the literal binary
augmentation hyperplane of four points. -/
theorem augmentation_elementFixedSpace_finrank_le_one_of_order_three
    (hcard : Nat.card X = 4)
    (S : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G X))
    (hS : S.toSubmodule = PermutationAugmentation.space (ZMod 2) X)
    (g : G) (hg : orderOf (MulAction.toPermHom G X g) = 3) :
    Module.finrank (ZMod 2)
      (representationElementFixedSpace S.toRepresentation g) ≤ 1 := by
  let σ : Equiv.Perm X := MulAction.toPermHom G X g
  have hcycle : σ.IsCycle := isThreeCycle_of_order_three_on_four hcard g hg
  have hsupp : σ.support.card = 3 := by
    rw [← hcycle.orderOf]
    exact hg
  have hcomp : σ.supportᶜ.card = 1 := by
    rw [Finset.card_compl, Fintype.card_eq_nat_card, hcard, hsupp]
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcomp
  let x : X := Classical.choose hcycle
  have hxne : σ x ≠ x := (Classical.choose_spec hcycle).1
  have hx : x ∈ σ.support := Equiv.Perm.mem_support.mpr hxne
  let ev : representationElementFixedSpace S.toRepresentation g →ₗ[ZMod 2]
      ZMod 2 := {
    toFun := fun f => f.1.1 y
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hconst (f : representationElementFixedSpace S.toRepresentation g)
      {z : X} (hz : z ∈ σ.support) : f.1.1 z = f.1.1 x := by
    have hzne : σ z ≠ z := Equiv.Perm.mem_support.mp hz
    obtain ⟨i, hi⟩ := hcycle.exists_pow_eq hxne hzne
    let F : representationElementFixedSpace
        (permutationFunctionRepresentation (ZMod 2) G X) g :=
      ⟨f.1.1, (mem_representationElementFixedSpace _ _ _).mpr
        (congrArg Subtype.val
          ((mem_representationElementFixedSpace _ _ _).mp f.property))⟩
    let a : Subgroup.zpowers g :=
      ⟨g ^ i, Subgroup.pow_mem _ (Subgroup.mem_zpowers g) i⟩
    have hv := permutationElementFixed_apply_smul g F a x
    have hi' : (g ^ i) • x = z := by
      change (MulAction.toPermHom G X (g ^ i)) x = z
      rw [map_pow]
      exact hi
    change F.1 ((g ^ i) • x) = F.1 x at hv
    rw [hi'] at hv
    exact hv
  have hev : Function.Injective ev := by
    intro f f' he
    let d := f - f'
    have hdy : d.1.1 y = 0 := by
      change f.1.1 y - f'.1.1 y = 0
      exact sub_eq_zero.mpr he
    have hdaug : PermutationAugmentation.coordinateSum (ZMod 2) X d.1.1 = 0 := by
      have hdmem : d.1.1 ∈ PermutationAugmentation.space (ZMod 2) X := by
        rw [← hS]
        exact d.1.property
      exact hdmem
    have hsumsupp : ∑ z ∈ σ.support, d.1.1 z = d.1.1 x := by
      calc
        ∑ z ∈ σ.support, d.1.1 z =
            ∑ _z ∈ σ.support, d.1.1 x := by
          apply Finset.sum_congr rfl
          intro z hz
          exact hconst d hz
        _ = σ.support.card • d.1.1 x := by simp
        _ = d.1.1 x := by
          rw [hsupp]
          calc
            3 • d.1.1 x = 2 • d.1.1 x + d.1.1 x := by
              rw [show (3 : ℕ) = 2 + 1 by omega, add_nsmul, one_nsmul]
            _ = d.1.1 x := by
              rw [ZModModule.char_nsmul_eq_zero, zero_add]
    have hsumcomp : ∑ z ∈ σ.supportᶜ, d.1.1 z = d.1.1 y := by
      rw [hy]
      simp
    change (∑ z, d.1.1 z) = 0 at hdaug
    rw [← Finset.union_compl σ.support,
      Finset.sum_union disjoint_compl_right, hsumsupp, hsumcomp] at hdaug
    have hdx : d.1.1 x = 0 := by
      rw [hdy, add_zero] at hdaug
      exact hdaug
    apply Subtype.ext
    apply Subtype.ext
    funext z
    by_cases hz : z ∈ σ.support
    · have hdz : d.1.1 z = 0 := (hconst d hz).trans hdx
      change f.1.1 z - f'.1.1 z = 0 at hdz
      exact sub_eq_zero.mp hdz
    · have hzy : z = y := by
        have : z ∈ σ.supportᶜ := by simpa using hz
        rw [hy] at this
        simpa using this
      subst z
      change f.1.1 y - f'.1.1 y = 0 at hdy
      exact sub_eq_zero.mp hdy
  have hdim := ev.finrank_le_finrank_of_injective hev
  simpa only [Module.finrank_self] using hdim

/-- Hence every invariant-form head inside the four-point augmentation
hyperplane is at most one when the action image is nonbinary. -/
theorem four_nonbinary_subrepresentationHead_le_one
    (hcard : Nat.card X = 4)
    (hnon : ¬IsPGroup 2 (MulAction.toPermHom G X).range)
    (S : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G X))
    (hS : S.toSubmodule = PermutationAugmentation.space (ZMod 2) X) :
    Module.finrank (ZMod 2) (S.toRepresentation.IntertwiningMap
      (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ 1 := by
  obtain ⟨g, hg⟩ := exists_order_three_permutation_of_four_nonbinary hcard hnon
  exact (representationHead_le_elementFixedSpace S.toRepresentation g).trans
    (augmentation_elementFixedSpace_finrank_le_one_of_order_three hcard S hS g hg)

end SymmetricSubgroupAsymptotics

end
