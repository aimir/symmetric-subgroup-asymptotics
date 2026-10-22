import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.GroupAction.Quotient

/-! A Sylow two-subgroup of an alternating group of positive even degree
cannot fix a point. This uses the actual point-stabilizer index and Sylow
index coprimality, with no catalogue or classification input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingSylowNoFixedPoint

theorem exists_move
    {X : Type*} [Fintype X] (hsize : 3 ≤ Nat.card X) (heven : 2 ∣ Nat.card X)
    (P : Sylow 2 (alternatingGroup X)) (x : X) : ∃ g : P, g • x ≠ x := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction.IsPretransitive (alternatingGroup X) X :=
    alternatingGroup.isPretransitive_of_three_le_card X hsize
  by_contra h
  push_neg at h
  have hle : (P : Subgroup (alternatingGroup X)) ≤
      MulAction.stabilizer (alternatingGroup X) x := by
    intro g hg
    exact h ⟨g, hg⟩
  have hd := Subgroup.index_dvd_of_le hle
  have hi : (MulAction.stabilizer (alternatingGroup X) x).index = Nat.card X :=
    MulAction.index_stabilizer_of_transitive (alternatingGroup X) x
  rw [hi] at hd
  exact P.not_dvd_index (heven.trans hd)

end SymmetricSubgroupAsymptotics.CFSGAlternatingSylowNoFixedPoint
