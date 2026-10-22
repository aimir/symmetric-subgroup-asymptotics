import SymmetricSubgroupAsymptotics.CFSGSupportedPrimitiveAction
import Mathlib.GroupTheory.GroupAction.Jordan
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! A transitive permutation group containing the actual alternating
group on more than half its points contains the full alternating group.
The supported action is built from extension by the identity. Primitivity
is proved by blocks; the final three-cycle step is Mathlib's Jordan theorem.
No simple-group classification or unspecified support-gluing input is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.CFSGSupportedAlternatingGeneration
open MulAction Equiv

def supportedHom {X : Type*} [Fintype X] [DecidableEq X] (S : Finset X) :
    alternatingGroup S →* Perm X :=
  (Perm.ofSubtype : Perm S →* Perm X).comp (alternatingGroup S).subtype

theorem isPreprimitive_of_supported_alternating
    {X : Type*} [Fintype X] [DecidableEq X]
    (G : Subgroup (Perm X)) [IsPretransitive G X] (S : Finset X)
    (hsize : 3 ≤ S.card) (hhalf : Nat.card X < 2 * S.card)
    (hS : (supportedHom S).range ≤ G) : IsPreprimitive G X := by
  let rho : alternatingGroup S →* G := (supportedHom S).codRestrict G
    (fun a => hS ⟨a, rfl⟩)
  let K : Subgroup G := rho.range
  let A : SubMulAction K X := {
    carrier := (S : Set X)
    smul_mem' := by
      intro k x hx
      obtain ⟨a, ha⟩ := k.property
      have he : (k.val.val : Perm X) = Perm.ofSubtype (a : Perm S) := by
        exact (congrArg (fun g : G => (g : Perm X)) ha).symm
      change (k.val.val : Perm X) x ∈ S
      rw [he, Perm.ofSubtype_apply_of_mem _ hx]
      exact (a.val ⟨x, hx⟩).property }
  let e : S ≃ A := {
    toFun x := ⟨x, x.property⟩
    invFun x := ⟨x, x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hc : 3 ≤ Nat.card S := by simpa using hsize
  letI : Nontrivial S := by
    apply Fintype.one_lt_card_iff_nontrivial.mp
    simpa only [Fintype.card_coe] using (show 1 < S.card by omega)
  letI : Nontrivial A := e.nontrivial
  letI : IsPreprimitive (alternatingGroup S) S :=
    alternatingGroup.isPreprimitive_of_three_le_card S hc
  let f : S →ₑ[rho.rangeRestrict] A := {
    toFun := e
    map_smul' := by
      intro a x
      apply Subtype.ext
      change (a.val x).val = (Perm.ofSubtype a.val) x.val
      exact (Perm.ofSubtype_apply_of_mem a.val x.property).symm }
  letI : IsPreprimitive K A := IsPreprimitive.of_surjective (f := f) e.surjective
  apply CFSGSupportedPrimitiveAction.isPreprimitive_of_large_supported_subaction K A
  · intro k x hx
    obtain ⟨a, ha⟩ := k.property
    have he : (k.val.val : Perm X) = Perm.ofSubtype (a : Perm S) :=
      (congrArg (fun g : G => (g : Perm X)) ha).symm
    change (k.val.val : Perm X) x = x
    rw [he]
    exact Perm.ofSubtype_apply_of_not_mem _ hx
  · change Nat.card X < (S : Set X).ncard * 2
    rw [Set.ncard_coe_finset]
    omega

theorem alternatingGroup_le_of_supported_alternating
    {X : Type*} [Fintype X] [DecidableEq X]
    (G : Subgroup (Perm X)) [IsPretransitive G X] (S : Finset X)
    (hsize : 3 ≤ S.card) (hhalf : Nat.card X < 2 * S.card)
    (hS : (supportedHom S).range ≤ G) : alternatingGroup X ≤ G := by
  letI := isPreprimitive_of_supported_alternating G S hsize hhalf hS
  have hthree : 2 < (S : Set X).ncard := by simpa using hsize
  rw [Set.two_lt_ncard_iff] at hthree
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hthree
  let t : Perm S := Equiv.swap ⟨a, ha⟩ ⟨b, hb⟩ * Equiv.swap ⟨a, ha⟩ ⟨c, hc⟩
  have ht : Perm.IsThreeCycle t := Perm.isThreeCycle_swap_mul_swap_same
    (fun h => hab (congrArg Subtype.val h))
    (fun h => hac (congrArg Subtype.val h))
    (fun h => hbc (congrArg Subtype.val h))
  let u : alternatingGroup S := ⟨t, ht.mem_alternatingGroup⟩
  have hu : Perm.IsThreeCycle (supportedHom S u) := by
    change Perm.IsThreeCycle (Perm.ofSubtype t)
    change Perm.IsThreeCycle (Perm.ofSubtype
      (Equiv.swap (⟨a, ha⟩ : S) ⟨b, hb⟩ * Equiv.swap (⟨a, ha⟩ : S) ⟨c, hc⟩))
    rw [map_mul, Perm.ofSubtype_swap_eq, Perm.ofSubtype_swap_eq]
    exact Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  exact Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
    inferInstance hu (hS ⟨u, rfl⟩)

end SymmetricSubgroupAsymptotics.CFSGSupportedAlternatingGeneration
