import SymmetricSubgroupAsymptotics.OriginalBinaryAffineDominantPrimeTail
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineZeroMatchingPrimeTail
import SymmetricSubgroupAsymptotics.BinaryGeneralLinearSmallPrimeSupport

/-! An honest finite PRIME/EXPONENT frontier for the ORIGINAL action.
The conclusion is a proved rank bound OR a literal arithmetic witness,
not an assumed frontier or a completed Tracey theorem. The actual top
can remain large; its complementary coordinate is controlled by the
checked endpoint proofs, not enumerated as an integer degree. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineFiniteDominantFrontier
open OriginalAffineBlockCharacteristicHead

theorem small_prime_power_parameters (q a : ℕ) (hq : q.Prime)
    (ha : 1 ≤ a) (hpow : q^a < 64) : q < 64 ∧ a < 6 := by
  have hqpow : q ≤ q^a := by
    simpa only [pow_one] using Nat.pow_le_pow_right hq.pos ha
  have h2pow := Nat.pow_le_pow_left hq.two_le a
  have ha' : (2 : ℕ)^a < (2 : ℕ)^6 := by
    simpa only [show (2 : ℕ)^6 = 64 by decide] using h2pow.trans_lt hpow
  exact ⟨hqpow.trans_lt hpow,
    (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).mp ha'⟩

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_ceiling_or_finite_frontier (hp : P.p = 2)
    (hd6 : translationDimension J block P ≤ 6) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      ∃ q ∈ (Fintype.card block.Points).primeFactors,
        (∀ r ∈ (Fintype.card block.Points).primeFactors,
          r^(Fintype.card block.Points).factorization r ≤
            q^(Fintype.card block.Points).factorization q) ∧
        ((q ∈ ({2,3,5,7,31} : Finset ℕ) ∧
          (Fintype.card block.Points).factorization q < 512) ∨
          (q < 64 ∧ (Fintype.card block.Points).factorization q < 6)) := by
  let t := Fintype.card block.Points
  have ht : 2 ≤ t := by
    simpa only [t,Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  obtain ⟨q,hq,hmax⟩ := LargestPrimePowerEntropy.exists_largest_prime_power t ht
  by_cases ha : 512 ≤ t.factorization q
  · exact Or.inl (OriginalBinaryAffineDominantPrimeTail.genRank_le_ceiling_of_dominant_exponent
      J block P hp hd6 i q hq ha hmax htop)
  · by_cases hsupport : q ∈ ({2,3,5,7,31} : Finset ℕ)
    · exact Or.inr ⟨q,hq,hmax,Or.inl ⟨hsupport,lt_of_not_ge ha⟩⟩
    · by_cases hM : 64 ≤ q^t.factorization q
      · have hzero := BinaryGeneralLinearSmallPrimeSupport.matchingMultiplicity_eq_zero
          (translationDimension J block P) q hd6 hsupport
        exact Or.inl (OriginalBinaryAffineZeroMatchingPrimeTail.genRank_le_ceiling_of_zero_matching
          J block P hp hd6 i q hq hmax hM hzero htop)
      · have hqprime := Nat.prime_of_mem_primeFactors hq
        have haq : 1 ≤ t.factorization q := by
          have hh : t.factorization q ≠ 0 := Finsupp.mem_support_iff.mp hq
          omega
        exact Or.inr ⟨q,hq,hmax,Or.inr (small_prime_power_parameters q
          (t.factorization q) hqprime haq (lt_of_not_ge hM))⟩

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineFiniteDominantFrontier
