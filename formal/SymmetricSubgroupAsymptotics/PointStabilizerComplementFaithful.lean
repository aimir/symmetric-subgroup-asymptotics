import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer

/-! Restricting a faithful action's point stabilizer to the complement
of that point remains faithful. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.PointStabilizerComplementFaithful

theorem faithfulSMul (G X : Type) [Group G] [MulAction G X] [FaithfulSMul G X]
    (x : X) : FaithfulSMul (MulAction.stabilizer G x) (SubMulAction.ofStabilizer G x) := by
  constructor
  intro g h he
  apply Subtype.ext
  apply eq_of_smul_eq_smul (α := X)
  intro z
  by_cases hz : z=x
  · subst z
    exact g.property.trans h.property.symm
  · exact congrArg Subtype.val (he ⟨z,hz⟩)

end SymmetricSubgroupAsymptotics.PointStabilizerComplementFaithful
