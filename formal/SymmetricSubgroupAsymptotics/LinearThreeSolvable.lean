import SymmetricSubgroupAsymptotics.Non2PreE7LinearThreeGroup
import Mathlib.GroupTheory.Solvable

/-!
# Solvability of `GL₂(3)`

The literal projective representation already constructed in
`Non2PreE7LinearThreeGroup` exhibits `GL₂(3)` as a central extension of
`S₄` by a group of order two.  This file records the resulting solvability
theorem so that the degree-nine primitive affine argument does not need a
catalogue assumption.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The natural symmetric group on four letters is soluble: its second
derived subgroup is the Klein four group. -/
theorem naturalS4_isSolvable : IsSolvable (Equiv.Perm (Fin 4)) := by
  refine ⟨⟨3, ?_⟩⟩
  rw [show 3 = 2 + 1 by norm_num, derivedSeries_succ,
    NaturalS4.derivedSeries_two]
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_eq_one_iff_mul_comm.mpr
    (NaturalS4.kleinSet_comm a ha b hb)]
  exact Subgroup.one_mem _

namespace LinearThree

/-- `GL₂(3)` is soluble, via its projective quotient `S₄` and central
kernel `{+I,-I}`. -/
theorem gl3_isSolvable : IsSolvable GL3 := by
  letI : IsSolvable (Equiv.Perm (Fin 4)) := naturalS4_isSolvable
  letI : IsSolvable projective.ker := isSolvable_of_comm (fun a b => by
    apply Subtype.ext
    exact central_of_ker a a.2 b)
  apply solvable_of_ker_le_range projective.ker.subtype projective
  intro g hg
  exact ⟨⟨g, hg⟩, rfl⟩

end LinearThree
end SymmetricSubgroupAsymptotics

end
