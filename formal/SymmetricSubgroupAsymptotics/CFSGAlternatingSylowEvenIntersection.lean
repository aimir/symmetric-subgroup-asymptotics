import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Sylow

/-! An alternating Sylow two-subgroup inside a symmetric Sylow is
exactly its even part, with the literal subtype embedding retained. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingSylowEvenIntersection
open Equiv

theorem comap_eq {X : Type*} [Fintype X] [DecidableEq X]
    (P : Sylow 2 (alternatingGroup X)) (Q : Sylow 2 (Perm X))
    (hPQ : (P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype ≤ Q) :
    (Q : Subgroup (Perm X)).comap (alternatingGroup X).subtype =
      (P : Subgroup (alternatingGroup X)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply P.is_maximal' (Q.isPGroup'.comap_of_injective _ (alternatingGroup X).subtype_injective)
  intro g hg
  exact hPQ ⟨g, hg, rfl⟩

theorem mem_ambient_iff {X : Type*} [Fintype X] [DecidableEq X]
    (P : Sylow 2 (alternatingGroup X)) (Q : Sylow 2 (Perm X))
    (hPQ : (P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype ≤ Q)
    (g : Perm X) :
    g ∈ (P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype ↔
      g ∈ Q ∧ g ∈ alternatingGroup X := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨hPQ ⟨a, ha, rfl⟩, a.property⟩
  · rintro ⟨hg, he⟩
    refine ⟨⟨g, he⟩, ?_, rfl⟩
    have hh : (⟨g, he⟩ : alternatingGroup X) ∈
        (Q : Subgroup (Perm X)).comap (alternatingGroup X).subtype := hg
    rwa [comap_eq P Q hPQ] at hh

end SymmetricSubgroupAsymptotics.CFSGAlternatingSylowEvenIntersection
