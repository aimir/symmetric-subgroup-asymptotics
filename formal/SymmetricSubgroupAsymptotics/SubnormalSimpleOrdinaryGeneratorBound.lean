import SymmetricSubgroupAsymptotics.GoodSylowPermutationOrdinaryGenerators
import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators
import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators
import Mathlib.GroupTheory.IsSubnormal

/-! Ordinary generator bounds across the SAME actual simple normal
subgroup, uniformly for original subnormal subgroups. Restricting the
actual quotient map gives a kernel isomorphic to the actual intersection
inside the simple subgroup. Only ordinary kernel/quotient subadditivity
is used. No simple two-generation or extension splitting is assumed. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.SubnormalSimpleOrdinaryGeneratorBound

variable {G : Type} [Group G]

def restrictionKernelEquiv (S N : Subgroup G) [S.Normal] :
    ((QuotientGroup.mk' S).comp N.subtype).ker ≃* N.subgroupOf S where
  toFun x := ⟨⟨x.val.val,(QuotientGroup.eq_one_iff x.val.val).mp x.property⟩,
    x.val.property⟩
  invFun x := ⟨⟨x.val.val,x.property⟩,
    (QuotientGroup.eq_one_iff x.val.val).mpr x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem genRank_le_simple_add_quotient_budget [Finite G]
    (S : Subgroup G) [S.Normal] [IsSimpleGroup S] (a b : ℕ)
    (hS : MarkedC4.genRank S ≤ a) (hquot : Nat.card (G ⧸ S) ≤ 2^b)
    (N : Subgroup G) (hN : N.IsSubnormal) : MarkedC4.genRank N ≤ a+b := by
  let f := (QuotientGroup.mk' S).comp N.subtype
  let e := restrictionKernelEquiv S N
  have hquotient : MarkedC4.genRank (N ⧸ f.ker) ≤ b := by
    apply FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow
    exact (Nat.card_le_card_of_injective (QuotientGroup.kerLift f)
      (QuotientGroup.kerLift_injective f)).trans hquot
  have hkernel : MarkedC4.genRank f.ker ≤ a := by
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup
        (inferInstance : IsSimpleGroup S)
        (hN.subgroupOf : (N.subgroupOf S).IsSubnormal) with hzero | hfull
    · have hcard : Nat.card f.ker = 1 := by
        calc
          Nat.card f.ker = Nat.card (N.subgroupOf S) := Nat.card_congr e.toEquiv
          _ = 1 := by rw [hzero]; exact Nat.card_unique
      have hz : MarkedC4.genRank f.ker ≤ 0 :=
        FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow f.ker 0
          (by simpa only [pow_zero] using hcard.le)
      exact hz.trans (Nat.zero_le a)
    · let eS : f.ker ≃* S :=
        e.trans ((MulEquiv.subgroupCongr hfull).trans Subgroup.topEquiv)
      exact (CoprimeNilpotentProductGenerators.genRank_mulEquiv eS).le.trans hS
  exact (MarkedC4.genRank_le_of_normal f.ker).trans
    (Nat.add_le_add hkernel hquotient)

/-- The displayed subgroup and conjugating element genuinely generate
the simple normal subgroup. Its ordinary cost is retained explicitly. -/
theorem genRank_le_of_two_conjugates [Finite G]
    (S : Subgroup G) [S.Normal] [IsSimpleGroup S]
    (P : Subgroup S) (g : S)
    (hgen : Subgroup.closure ((P : Set S) ∪ P.map (MulAut.conj g).toMonoidHom) = ⊤)
    (a b : ℕ) (hP : MarkedC4.genRank P ≤ a) (hquot : Nat.card (G ⧸ S) ≤ 2^b)
    (N : Subgroup G) (hN : N.IsSubnormal) : MarkedC4.genRank N ≤ a+1+b := by
  apply genRank_le_simple_add_quotient_budget S (a+1) b ?_ hquot N hN
  exact (TwoConjugateSubgroupsOrdinaryGenerators.genRank_le_add_one P g hgen).trans
    (Nat.add_le_add_right hP 1)

/-- Optional faithful-degree estimate. Literal cyclic or prime-order
Sylow information can improve it through the preceding theorem. -/
theorem genRank_le_degree_div_add_budget [Finite G]
    {X : Type} [Finite X] [MulAction G X] [FaithfulSMul G X]
    (S : Subgroup G) [S.Normal] [IsSimpleGroup S] (p b : ℕ)
    (hgood : CFSGReduction.GoodSylowPrime S p) (hquot : Nat.card (G ⧸ S) ≤ 2^b)
    (N : Subgroup G) (hN : N.IsSubnormal) :
    MarkedC4.genRank N ≤ Nat.card X/p+1+b := by
  obtain ⟨hp,P,g,_,hgen⟩ := hgood
  letI : Fact p.Prime := ⟨hp⟩
  exact genRank_le_of_two_conjugates S (P : Subgroup S) g hgen
    (Nat.card X/p) b
    (PermutationPGroupOrdinaryGenerators.genRank_le_degree_div p P X P.isPGroup')
    hquot N hN

end SymmetricSubgroupAsymptotics.SubnormalSimpleOrdinaryGeneratorBound
