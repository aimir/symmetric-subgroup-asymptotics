import SymmetricSubgroupAsymptotics.OriginalBinaryAffineSmallPrimaryComplementStep
import SymmetricSubgroupAsymptotics.SmallPrimaryTinyComplementDegree

/-! The checked all-dimension large-complement step leaves a literal
bounded factorization state on the ORIGINAL action. The quotient factor
k is the actual prime-to-q part, not a free certificate parameter. This
is a frontier theorem, not a completed coarse Tracey bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyComplementFrontier
open OriginalAffineBlockCharacteristicHead

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_ceiling_or_actual_tiny_data (hp : P.p = 2) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      ∃ q ∈ (Fintype.card block.Points).primeFactors,
        q ∈ ({2,3,5,7,31} : Finset ℕ) ∧
        (∀ r ∈ (Fintype.card block.Points).primeFactors,
          r^(Fintype.card block.Points).factorization r ≤
            q^(Fintype.card block.Points).factorization q) ∧
        q^(Fintype.card block.Points).factorization q < 64 ∧
        translationDimension J block P ≤ 6 ∧
        (∀ r ∈ (Fintype.card block.Points).primeFactors, r ≠ q →
          r^(Fintype.card block.Points).factorization r ≤ 4) ∧
        ∃ k : ℕ, 1 ≤ k ∧ k ∣ 12 ∧
          Nat.Coprime (q^(Fintype.card block.Points).factorization q) k ∧
          Fintype.card block.Points = q^(Fintype.card block.Points).factorization q*k ∧
          Fintype.card block.Points ≤ 756 := by
  by_cases hd6 : translationDimension J block P ≤ 6
  · obtain hbound | ⟨q,hq,hsupport,hmax,hM64,hother⟩ :=
      OriginalBinaryAffineSmallPrimaryComplementStep.genRank_le_ceiling_or_small_complement
        J block P hp i htop
    · exact Or.inl hbound
    · have ht0 : Fintype.card block.Points ≠ 0 := Fintype.card_ne_zero
      obtain ⟨k,hk1,hk12,hcop,hshape⟩ := SmallPrimaryTinyComplementDegree.degree_data
        q (Fintype.card block.Points) (Nat.prime_of_mem_primeFactors hq) ht0 hother
      exact Or.inr ⟨q,hq,hsupport,hmax,hM64,hd6,hother,k,hk1,hk12,hcop,hshape,
        SmallPrimaryTinyComplementDegree.degree_le q (Fintype.card block.Points) ht0 hM64 hother⟩
  · exact Or.inl (OriginalBinaryAffineArbitraryTopTail.genRank_le_ceiling_of_dimension_ge_seven
      J block P hp (by omega) i htop)

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyComplementFrontier
