import SymmetricSubgroupAsymptotics.BinaryThirtyTwoHeadThreeNormalFProof
import SymmetricSubgroupAsymptotics.RDTNormalFThirtyTwoCriticalFourFive
import SymmetricSubgroupAsymptotics.RDTNormalFThirtyTwoTargetAssembly

/-! The full binary normal-F theorem, with no mathematical hypotheses.
The original literal action, normal denominator, ambient mixed commutator,
centralizer, exact excess alternatives and rank-preservation condition are
those of the published interface. All degree and critical clauses are
supplied by checked original-action proofs, not by extra premises. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem publishedTheorem57Binary_proved :
    MarkedC4.RDTExcessStructure.PublishedTheorem57Binary :=
  publishedTheorem57Binary_of_critical_clauses
    binaryThirtyTwoCriticalHeadThreeTopSixNormalF_proved
    binary_thirty_two_critical_head_four_top_five_normalF_proved

end SymmetricSubgroupAsymptotics
