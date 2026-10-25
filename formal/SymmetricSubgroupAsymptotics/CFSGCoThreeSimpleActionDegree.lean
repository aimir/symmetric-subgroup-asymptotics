import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedWordOrder
import SymmetricSubgroupAsymptotics.PerfectPermutationTwicePrimeOrderDegree
import SymmetricSubgroupAsymptotics.PerfectSubdirect

/-! The SAME selected Co3 element has14-divisible order. Whenever this
actual model is nonabelian simple, perfectness forces its faithful
permutation images to be even, hence to occupy at least11points. No new
word, vector, model order or catalogue information is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCoThreeSimpleActionDegree

theorem eleven_le_card_of_faithful_action {X : Type*} [Fintype X] [DecidableEq X]
    [IsSimpleGroup CFSG.Models.MatrixGroups.Co3.Model]
    (hn : ¬ IsMulCommutative CFSG.Models.MatrixGroups.Co3.Model)
    (f : CFSG.Models.MatrixGroups.Co3.Model →* Equiv.Perm X)
    (hf : Function.Injective f) : 11 ≤ Nat.card X := by
  letI : Group.IsPerfect CFSG.Models.MatrixGroups.Co3.Model := simple_perfect_of_nonabelian hn
  obtain ⟨g,hg⟩ := CFSGCoThreeSelectedWordOrder.exists_fourteen_dvd_orderOf hn
  exact PerfectPermutationTwicePrimeOrderDegree.eleven_le_card_of_faithful_action f hf g hg

end SymmetricSubgroupAsymptotics.CFSGCoThreeSimpleActionDegree
