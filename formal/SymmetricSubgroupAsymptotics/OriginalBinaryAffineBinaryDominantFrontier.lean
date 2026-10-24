import SymmetricSubgroupAsymptotics.OriginalBinaryAffineOddSmallComplementTail
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineSmallComplementFrontier

/-! All odd dominant powers at least64 are discharged on the original
action. The remaining arithmetic witnesses are a genuinely small dominant
power or a binary dominant power with small complementary powers. This
is a proved reduction, not a completed Tracey theorem or a fit assumption. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineBinaryDominantFrontier
open OriginalAffineBlockCharacteristicHead

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_ceiling_or_binary_frontier (hp : P.p = 2)
    (hd6 : translationDimension J block P ≤ 6) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      ∃ q ∈ (Fintype.card block.Points).primeFactors,
        (∀ r ∈ (Fintype.card block.Points).primeFactors,
          r^(Fintype.card block.Points).factorization r ≤
            q^(Fintype.card block.Points).factorization q) ∧
        (q^(Fintype.card block.Points).factorization q < 64 ∨
          (q = 2 ∧ 6 ≤ (Fintype.card block.Points).factorization q ∧
            (Fintype.card block.Points).factorization q < 128 ∧
            ∀ r ∈ (Fintype.card block.Points).primeFactors, r ≠ q →
              r^(Fintype.card block.Points).factorization r < 16)) := by
  obtain hbound | ⟨q,hq,hmax,hsmall | ⟨_,ha,hother⟩⟩ :=
    OriginalBinaryAffineSmallComplementFrontier.genRank_le_ceiling_or_small_complement
      J block P hp hd6 i htop
  · exact Or.inl hbound
  · exact Or.inr ⟨q,hq,hmax,Or.inl hsmall⟩
  · by_cases hM : 64 ≤ q^(Fintype.card block.Points).factorization q
    · by_cases hq2 : q = 2
      · have hpow : (2 : ℕ)^6 ≤ 2^(Fintype.card block.Points).factorization q := by
          simpa only [hq2,show (2 : ℕ)^6 = 64 by decide] using hM
        have ha6 : 6 ≤ (Fintype.card block.Points).factorization q :=
          (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hpow
        exact Or.inr ⟨q,hq,hmax,Or.inr ⟨hq2,ha6,ha,hother⟩⟩
      · exact Or.inl
          (OriginalBinaryAffineOddSmallComplementTail.genRank_le_ceiling_of_odd_primary
            J block P hp hd6 i q hq hq2 hM hother htop)
    · exact Or.inr ⟨q,hq,hmax,Or.inl (lt_of_not_ge hM)⟩

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineBinaryDominantFrontier
