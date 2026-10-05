import SymmetricSubgroupAsymptotics.FiniteConjugacyCover
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Sparse conjugacy coverage from class cardinalities

Large finite permutation groups should not be certified by listing every
element.  A selected representative list is complete as soon as its classes
are pairwise distinct and the sum of their literal cardinalities is the order
of the group.  This file turns precisely those two finite checks into an
actual conjugacy cover.

The intended certificates compute each class cardinality from a checked
centralizer and never enumerate the carrier of the original group.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] [Finite G] {c : ℕ}

/-- A sparse list of pairwise distinct conjugacy classes whose cardinalities
exhaust the literal finite group. -/
structure FiniteConjugacyCardinalCover
    (representative : Fin c → G) : Prop where
  separated : ∀ i j, IsConj (representative i) (representative j) → i = j
  class_card_sum :
    (∑ i : Fin c, Nat.card {x : G // IsConj x (representative i)}) =
      Nat.card G

namespace FiniteConjugacyCardinalCover

variable {representative : Fin c → G}
    (C : FiniteConjugacyCardinalCover representative)

/-- Forget the selected class label and retain its literal element. -/
def coverMap : (Σ i : Fin c, {x : G // IsConj x (representative i)}) → G
  | ⟨_, x⟩ => x

include C

omit [Finite G] in
theorem coverMap_injective :
    Function.Injective (coverMap (representative := representative)) := by
  intro x y hxy
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  have hval : (x : G) = (y : G) := by
    simpa only [coverMap] using hxy
  have hconj : IsConj (representative i) (representative j) := by
    have hy : IsConj (x : G) (representative j) := by
      rw [hval]
      exact y.property
    exact x.property.symm.trans hy
  have hij : i = j := C.separated i j hconj
  subst j
  have hsub : x = y := Subtype.ext hval
  subst y
  rfl

/-- Equality of the selected class sum with the group order upgrades the
obvious injection of the disjoint selected classes to a surjection. -/
theorem coverMap_surjective :
    Function.Surjective (coverMap (representative := representative)) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI (i : Fin c) : Fintype {x : G // IsConj x (representative i)} :=
    Fintype.ofFinite _
  by_contra hsurj
  have hlt := Fintype.card_lt_of_injective_not_surjective
    (coverMap (representative := representative))
    C.coverMap_injective hsurj
  have heq :
      Fintype.card (Σ i : Fin c, {x : G // IsConj x (representative i)}) =
        Fintype.card G := by
    rw [Fintype.card_sigma]
    simpa only [Nat.card_eq_fintype_card] using C.class_card_sum
  exact (ne_of_lt hlt) heq

/-- Every literal element is conjugate to exactly one selected label.  Only
existence is needed by the normal-subgroup registry. -/
theorem covers (x : G) : ∃ i, IsConj x (representative i) := by
  obtain ⟨⟨i, y⟩, hy⟩ := C.coverMap_surjective x
  refine ⟨i, ?_⟩
  rw [← hy]
  exact y.property

omit C [Finite G] in
/-- A normal subgroup containing an element also contains the selected
representative of its conjugacy class. -/
theorem representative_mem_normal {N : Subgroup G} [N.Normal]
    {x : G} (hx : x ∈ N) {i : Fin c}
    (hxi : IsConj x (representative i)) : representative i ∈ N := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxi
  rw [← hg]
  exact Subgroup.Normal.conj_mem (H := N) inferInstance x hx g

end FiniteConjugacyCardinalCover
end SymmetricSubgroupAsymptotics

end
