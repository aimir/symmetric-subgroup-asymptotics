import SymmetricSubgroupAsymptotics.TwoConjugateSubgroupsOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PermutationPGroupOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrime

/-! The actual good-Sylow witness pays an ordinary generation bound in
its original faithful permutation action. Odd-prime witnesses give the
half-degree bound from degree six onward, without a simple-group
classification or a two-generator hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.GoodSylowPermutationOrdinaryGenerators

theorem genRank_le_degree_div_add_one {G X : Type} [Group G] [Finite G]
    [Finite X] [MulAction G X] [FaithfulSMul G X]
    (p : ℕ) (hgood : CFSGReduction.GoodSylowPrime G p) :
    MarkedC4.genRank G ≤ Nat.card X/p+1 := by
  obtain ⟨hp,P,g,_,hgen⟩ := hgood
  letI : Fact p.Prime := ⟨hp⟩
  exact (TwoConjugateSubgroupsOrdinaryGenerators.genRank_le_add_one
    (P:Subgroup G) g hgen).trans (Nat.add_le_add_right
      (PermutationPGroupOrdinaryGenerators.genRank_le_degree_div p P X P.isPGroup') 1)

theorem two_mul_genRank_le_degree {G X : Type} [Group G] [Finite G]
    [Finite X] [MulAction G X] [FaithfulSMul G X]
    (p : ℕ) (hp : 3 ≤ p) (hn : 6 ≤ Nat.card X)
    (hgood : CFSGReduction.GoodSylowPrime G p) :
    2*MarkedC4.genRank G ≤ Nat.card X := by
  have hr := genRank_le_degree_div_add_one (X:=X) p hgood
  have hd := Nat.mul_div_le (Nat.card X) p
  have hdiv : Nat.card X/p ≤ Nat.card X/3 := Nat.div_le_div_left hp (by omega)
  omega

theorem exists_half_degree_generators {G X : Type} [Group G] [Finite G]
    [Finite X] [MulAction G X] [FaithfulSMul G X]
    (p : ℕ) (hp : 3 ≤ p) (hn : 6 ≤ Nat.card X)
    (hgood : CFSGReduction.GoodSylowPrime G p) :
    ∃S : Finset G,Subgroup.closure (S:Set G)=⊤ ∧ 2*S.card≤Nat.card X := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  refine ⟨S,hgen,?_⟩
  rw [hS]
  exact two_mul_genRank_le_degree (X:=X) p hp hn hgood

end SymmetricSubgroupAsymptotics.GoodSylowPermutationOrdinaryGenerators
