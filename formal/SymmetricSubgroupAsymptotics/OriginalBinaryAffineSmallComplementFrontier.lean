import SymmetricSubgroupAsymptotics.OriginalBinaryAffineLargeComplementaryTail
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineReducedFiniteDominantFrontier

/-! A literal small-complement frontier for the original affine block
action. Every large dominant/large complementary pair is discharged by
proved actual ordinary costs and the actual top ceiling. The remaining
prime/exponent witnesses are conclusions, never assumed fit certificates. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineSmallComplementFrontier
open OriginalAffineBlockCharacteristicHead

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_ceiling_or_small_complement (hp : P.p = 2)
    (hd6 : translationDimension J block P ≤ 6) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      ∃ q ∈ (Fintype.card block.Points).primeFactors,
        (∀ r ∈ (Fintype.card block.Points).primeFactors,
          r^(Fintype.card block.Points).factorization r ≤
            q^(Fintype.card block.Points).factorization q) ∧
        (q^(Fintype.card block.Points).factorization q < 64 ∨
          (q ∈ ({2,3,5,7,31} : Finset ℕ) ∧
            (Fintype.card block.Points).factorization q < 128 ∧
            ∀ r ∈ (Fintype.card block.Points).primeFactors, r ≠ q →
              r^(Fintype.card block.Points).factorization r < 16)) := by
  let t := Fintype.card block.Points
  have ht : 2 ≤ t := by
    simpa only [t,Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  obtain ⟨q,hq,hmax⟩ := LargestPrimePowerEntropy.exists_largest_prime_power t ht
  by_cases ha : 128 ≤ t.factorization q
  · exact Or.inl
      (OriginalBinaryAffineReducedDominantPrimeTail.genRank_le_ceiling_of_dominant_exponent
        J block P hp hd6 i q hq ha hmax htop)
  · by_cases hM : 64 ≤ q^t.factorization q
    · by_cases hsupport : q ∈ ({2,3,5,7,31} : Finset ℕ)
      · by_cases hother : ∃ r ∈ t.primeFactors, r ≠ q ∧ 16 ≤ r^t.factorization r
        · exact Or.inl
            (OriginalBinaryAffineLargeComplementaryTail.genRank_le_ceiling_of_large_other_power
              J block P hp hd6 i q hq hsupport (lt_of_not_ge ha) hM hmax hother htop)
        · right
          refine ⟨q,hq,hmax,Or.inr ⟨hsupport,lt_of_not_ge ha,?_⟩⟩
          intro r hr hrq
          by_contra hh
          exact hother ⟨r,hr,hrq,le_of_not_gt hh⟩
      · have hzero := BinaryGeneralLinearSmallPrimeSupport.matchingMultiplicity_eq_zero
          (translationDimension J block P) q hd6 hsupport
        exact Or.inl
          (OriginalBinaryAffineZeroMatchingPrimeTail.genRank_le_ceiling_of_zero_matching
            J block P hp hd6 i q hq hmax hM hzero htop)
    · exact Or.inr ⟨q,hq,hmax,Or.inl (lt_of_not_ge hM)⟩

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineSmallComplementFrontier
