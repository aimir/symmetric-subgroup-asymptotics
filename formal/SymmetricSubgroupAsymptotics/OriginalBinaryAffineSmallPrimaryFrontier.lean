import SymmetricSubgroupAsymptotics.OriginalBinaryAffineThreeComplementInterval
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineFiveComplementInterval
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineSevenComplementInterval
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineBinaryDominantFrontier
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineArbitraryTopTail

/-! A small-primary frontier for the literal original binary affine
block action. Every large-primary case is discharged by proved actual
costs, retaining only the genuine smaller-top coarse ceiling. The
remaining small-primary condition is a conclusion, not a certificate
or an assumed scalar fitting bound. This is not a full Tracey proof. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineSmallPrimaryFrontier
open OriginalAffineBlockCharacteristicHead

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_ceiling_of_large_binary_small_complement (hp : P.p = 2)
    (hd6 : translationDimension J block P ≤ 6) (i : block.Points)
    (ha6 : 6 ≤ (Fintype.card block.Points).factorization 2)
    (hother : ∀ q ∈ (Fintype.card block.Points).primeFactors, q ≠ 2 →
      q^(Fintype.card block.Points).factorization q < 16)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let t := Fintype.card block.Points
  by_cases hseven : ∃ q ∈ t.primeFactors, q ≠ 2 ∧ 7 ≤ q^t.factorization q
  · exact OriginalBinaryAffineSevenComplementInterval.genRank_le_ceiling_of_some_other_power_seven
      J block P hp hd6 i ha6 hother hseven htop
  have hfive : ∀ q ∈ t.primeFactors, q ≠ 2 → q^t.factorization q ≤ 5 := by
    intro q hq hq2
    have hlt : q^t.factorization q < 7 := by
      by_contra hh
      exact hseven ⟨q,hq,hq2,le_of_not_gt hh⟩
    have hodd : Odd (q^t.factorization q) :=
      ((Nat.prime_of_mem_primeFactors hq).odd_of_ne_two hq2).pow
    obtain ⟨k,hk⟩ := hodd
    omega
  by_cases hexists : ∃ q ∈ t.primeFactors, q ≠ 2 ∧ 5 ≤ q^t.factorization q
  · exact OriginalBinaryAffineFiveComplementInterval.genRank_le_ceiling_of_other_powers_le_five
      J block P hp i ha6 hfive hexists htop
  have hthree : ∀ q ∈ t.primeFactors, q ≠ 2 → q^t.factorization q ≤ 3 := by
    intro q hq hq2
    have hlt : q^t.factorization q < 5 := by
      by_contra hh
      exact hexists ⟨q,hq,hq2,le_of_not_gt hh⟩
    have hodd : Odd (q^t.factorization q) :=
      ((Nat.prime_of_mem_primeFactors hq).odd_of_ne_two hq2).pow
    obtain ⟨k,hk⟩ := hodd
    omega
  exact OriginalBinaryAffineThreeComplementInterval.genRank_le_ceiling_of_other_powers_le_three
    J block P hp i ha6 hthree htop

theorem genRank_le_ceiling_or_small_primary (hp : P.p = 2) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      ∃ q ∈ (Fintype.card block.Points).primeFactors,
        (∀ r ∈ (Fintype.card block.Points).primeFactors,
          r^(Fintype.card block.Points).factorization r ≤
            q^(Fintype.card block.Points).factorization q) ∧
        q^(Fintype.card block.Points).factorization q < 64 := by
  by_cases hd6 : translationDimension J block P ≤ 6
  · obtain hbound | ⟨q,hq,hmax,hsmall | ⟨hq2,ha6,_,hother⟩⟩ :=
      OriginalBinaryAffineBinaryDominantFrontier.genRank_le_ceiling_or_binary_frontier
        J block P hp hd6 i htop
    · exact Or.inl hbound
    · exact Or.inr ⟨q,hq,hmax,hsmall⟩
    · subst q
      exact Or.inl (genRank_le_ceiling_of_large_binary_small_complement
        J block P hp hd6 i ha6 hother htop)
  · exact Or.inl
      (OriginalBinaryAffineArbitraryTopTail.genRank_le_ceiling_of_dimension_ge_seven
        J block P hp (by omega) i htop)

theorem genRank_le_ceiling_or_all_primary_powers_small (hp : P.p = 2) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      ∀ q ∈ (Fintype.card block.Points).primeFactors,
        q^(Fintype.card block.Points).factorization q < 64 := by
  obtain hbound | ⟨q,hq,hmax,hsmall⟩ :=
    genRank_le_ceiling_or_small_primary J block P hp i htop
  · exact Or.inl hbound
  · exact Or.inr (fun r hr => (hmax r hr).trans_lt hsmall)

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineSmallPrimaryFrontier
