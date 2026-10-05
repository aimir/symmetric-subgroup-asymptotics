import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A derangement in every finite nontrivial transitive action

This is the elementary Burnside-averaging seam used when applying Tracey's
orbitwise induced-module theorem.  The identity fixes every point.  If every
other group element fixed at least one point, the sum of the fixed-point
counts would be strictly larger than the group order, contradicting
Burnside's lemma for a transitive action.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A finite group acting transitively on a nontrivial finite set contains
an element with no fixed points. -/
theorem exists_fixedBy_eq_empty_of_pretransitive
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [MulAction.IsPretransitive G X]
    [Nontrivial X] :
    ∃ g : G, MulAction.fixedBy X g = ∅ := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype X := Fintype.ofFinite X
  let Ω := MulAction.orbitRel.Quotient G X
  letI : Fintype Ω := Fintype.ofFinite Ω
  letI : Unique Ω :=
    Classical.choice
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty G X).mp
        (inferInstance : MulAction.IsPretransitive G X))
  by_contra h
  push Not at h
  have hpositive (g : G) :
      1 ≤ Fintype.card (MulAction.fixedBy X g) := by
    rw [Nat.succ_le_iff, Fintype.card_pos_iff]
    obtain ⟨x, hx⟩ := h g
    exact ⟨⟨x, hx⟩⟩
  have hone :
      1 < Fintype.card (MulAction.fixedBy X (1 : G)) := by
    let e : MulAction.fixedBy X (1 : G) ≃ X := {
      toFun := Subtype.val
      invFun := fun x ↦ ⟨x, by simp⟩
      left_inv := fun x ↦ Subtype.ext rfl
      right_inv := fun _ ↦ rfl }
    rw [Fintype.card_congr e]
    exact Fintype.one_lt_card_iff_nontrivial.mpr
      (inferInstance : Nontrivial X)
  have hstrict :
      Fintype.card G <
        ∑ g : G, Fintype.card (MulAction.fixedBy X g) := by
    calc
      Fintype.card G = ∑ _g : G, 1 := by simp
      _ < ∑ g : G, Fintype.card (MulAction.fixedBy X g) :=
        Finset.sum_lt_sum
          (fun g _hg ↦ hpositive g)
          ⟨1, Finset.mem_univ _, hone⟩
  have hBurnside :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
  have hOrbit : Fintype.card Ω = 1 := Fintype.card_unique
  change (∑ a : G, Fintype.card (MulAction.fixedBy X a)) =
    Fintype.card Ω * Fintype.card G at hBurnside
  rw [hOrbit, one_mul] at hBurnside
  exact (Nat.lt_irrefl (Fintype.card G)) (hstrict.trans_eq hBurnside)

end SymmetricSubgroupAsymptotics

end
