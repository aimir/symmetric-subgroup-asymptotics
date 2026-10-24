import SymmetricSubgroupAsymptotics.PermutationPrimeGroupRank
import SymmetricSubgroupAsymptotics.PGroupGeneratorAbelianizationOrder

/-! The ordinary-generator half-degree theorem is unconditional for
every finite permutation p-group. The existing central-prime-block
induction bounds its character rank; actual Burnside lifts supply
ordinary generators in the same original group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PermutationPGroupOrdinaryGenerators

theorem genRank_le_degree_div (p : ℕ) [Fact p.Prime]
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (hG : IsPGroup p G) :
    MarkedC4.genRank G≤Nat.card X/p :=
  (pGroup_genRank_le_primeCharacterRank p hG).trans
    (permutationPGroup_primeCharacterRank_le p G X hG)

theorem exists_generating_finset (p : ℕ) [Fact p.Prime]
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (hG : IsPGroup p G) :
    ∃S : Finset G,Subgroup.closure (S:Set G)=⊤ ∧ p*S.card≤Nat.card X := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  refine ⟨S,hgen,?_⟩
  calc
    p*S.card≤p*(Nat.card X/p) :=
      Nat.mul_le_mul_left p (hS.le.trans (genRank_le_degree_div p G X hG))
    _≤Nat.card X := Nat.mul_div_le _ _

theorem exists_half_degree_generators (p : ℕ) [Fact p.Prime]
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (hG : IsPGroup p G) :
    ∃S : Finset G,Subgroup.closure (S:Set G)=⊤ ∧ 2*S.card≤Nat.card X := by
  obtain ⟨S,hS,hcard⟩ := exists_generating_finset p G X hG
  exact ⟨S,hS,(Nat.mul_le_mul_right S.card (Fact.out:p.Prime).two_le).trans hcard⟩

theorem subgroup_half_degree_generators (p n : ℕ) [Fact p.Prime]
    (J : Subgroup (Equiv.Perm (Fin n))) (hJ : IsPGroup p J) :
    ∃S : Finset J,Subgroup.closure (S:Set J)=⊤ ∧ 2*S.card≤n := by
  simpa only [Nat.card_fin] using exists_half_degree_generators p J (Fin n) hJ

end SymmetricSubgroupAsymptotics.PermutationPGroupOrdinaryGenerators
