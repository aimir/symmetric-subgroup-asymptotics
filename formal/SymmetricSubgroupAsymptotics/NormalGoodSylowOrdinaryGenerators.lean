import SymmetricSubgroupAsymptotics.GoodSylowPermutationOrdinaryGenerators
import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators

/-! A normal subgroup's actual odd-prime good-Sylow generators can be
combined with a literal binary order budget for the original quotient.
This uniform template applies in the original faithful action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NormalGoodSylowOrdinaryGenerators

theorem genRank_le_degree_div_add_budget {G X : Type} [Group G] [Finite G]
    [Finite X] [MulAction G X] [FaithfulSMul G X]
    (N : Subgroup G) [N.Normal] (p b : ℕ)
    (hgood : CFSGReduction.GoodSylowPrime N p)
    (hquot : Nat.card (G⧸N) ≤ 2^b) :
    MarkedC4.genRank G ≤ Nat.card X/p+1+b := by
  exact (MarkedC4.genRank_le_of_normal N).trans
    (Nat.add_le_add (GoodSylowPermutationOrdinaryGenerators.genRank_le_degree_div_add_one
      (X:=X) p hgood)
      (FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow (G⧸N) b hquot))

theorem two_mul_genRank_le_degree {G X : Type} [Group G] [Finite G]
    [Finite X] [MulAction G X] [FaithfulSMul G X]
    (N : Subgroup G) [N.Normal] (p b : ℕ) (hp : 3 ≤ p)
    (hn : 6*(b+1) ≤ Nat.card X)
    (hgood : CFSGReduction.GoodSylowPrime N p)
    (hquot : Nat.card (G⧸N) ≤ 2^b) :
    2*MarkedC4.genRank G ≤ Nat.card X := by
  have hr := genRank_le_degree_div_add_budget (X:=X) N p b hgood hquot
  have hdiv : Nat.card X/p ≤ Nat.card X/3 := Nat.div_le_div_left hp (by omega)
  omega

end SymmetricSubgroupAsymptotics.NormalGoodSylowOrdinaryGenerators
