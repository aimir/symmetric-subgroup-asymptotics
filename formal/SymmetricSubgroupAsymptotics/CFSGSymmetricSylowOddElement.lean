import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Sylow

/-! Every symmetric Sylow two-subgroup on at least two points has an
odd permutation. This is an index argument for the literal sign kernel. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGSymmetricSylowOddElement
open Equiv

theorem exists_odd {X : Type*} [Fintype X] [DecidableEq X]
    (hsize : 2 ≤ Nat.card X) (Q : Sylow 2 (Perm X)) :
    ∃ g : Perm X, g ∈ Q ∧ g ∉ alternatingGroup X := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  by_contra h
  push_neg at h
  have hle : (Q : Subgroup (Perm X)) ≤ alternatingGroup X := h
  have hi := Subgroup.index_dvd_of_le hle
  rw [alternatingGroup.index_eq_two] at hi
  exact Q.not_dvd_index hi

end SymmetricSubgroupAsymptotics.CFSGSymmetricSylowOddElement
