import SymmetricSubgroupAsymptotics.PrimitiveSocleIsotypicOrdinaryCompression
import SymmetricSubgroupAsymptotics.SimpleLeastIndexStrictOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGNonaffineCoarseComposition
import SymmetricSubgroupAsymptotics.FiniteGroupPrimeMultiplicityGenerators

/-! An independent ordinary recurrence retaining the ACTUAL primitive
socle quotient and its outer-wreath embedding. The genuine simple rank
is bounded only through a strictly-smaller faithful TRANSITIVE coset
action. Almost-simple minimum-degree actions are not included by that
strict step; no global permutation theorem or simple2generation is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleStrictOuterOrdinaryRecurrence
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

/-- Divisibility, not merely an order inequality, from the same quotient
embedding into its original outer wreath product. -/
theorem quotient_card_dvd_outer_wreath :
    Nat.card (G ⧸ finiteGroupSocle G) ∣
      Nat.card (Outer D.Simple)^D.factorCount * D.factorCount.factorial := by
  have hh := Subgroup.card_dvd_of_injective D.quotientEmbedding D.quotientEmbedding_injective
  simpa only [OuterWreathPermutationCompression.Wreath,PermutationalWreathProduct.natCard_eq,
    Nat.card_fin,Nat.card_perm] using hh

theorem quotient_genRank_le_outer_multiplicity :
    MarkedC4.genRank (G ⧸ finiteGroupSocle G) ≤
      D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
        ArithmeticFunction.cardFactors D.factorCount.factorial := by
  have hh := FiniteGroupPrimeMultiplicityGenerators.cardFactors_mono_of_dvd
    (Nat.card_pos (α := G ⧸ finiteGroupSocle G)).ne'
    (mul_ne_zero (pow_ne_zero _ (Nat.card_pos (α := Outer D.Simple)).ne')
      (Nat.factorial_pos D.factorCount).ne')
    (quotient_card_dvd_outer_wreath D)
  rw [ArithmeticFunction.cardFactors_mul
      (pow_ne_zero _ (Nat.card_pos (α := Outer D.Simple)).ne')
      (Nat.factorial_pos D.factorCount).ne',ArithmeticFunction.cardFactors_pow] at hh
  exact (FiniteGroupPrimeMultiplicityGenerators.genRank_le_cardFactors
    (G ⧸ finiteGroupSocle G)).trans hh

variable [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]

theorem genRank_le_strict_simple_add_actual_quotient (n ell : ℕ)
    (hbelow : SmallerTransitiveRankBound n) (hell : LeastProperIndex D.Simple ell)
    (hlt : ell < n) :
    MarkedC4.genRank G ≤ 2*traceyPermutationGeneratorCeiling ell+
      MarkedC4.genRank (G ⧸ finiteGroupSocle G) := by
  have hs := SimpleLeastIndexStrictOrdinaryGenerators.genRank_le_of_strictly_smaller
    D.Simple n ell hbelow hell hlt
  exact (PrimitiveSocleIsotypicOrdinaryCompression.genRank_le_twice_simple_add_quotient D).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hs) _)

theorem genRank_le_strict_simple_add_outer_multiplicity (n ell : ℕ)
    (hbelow : SmallerTransitiveRankBound n) (hell : LeastProperIndex D.Simple ell)
    (hlt : ell < n) :
    MarkedC4.genRank G ≤ 2*traceyPermutationGeneratorCeiling ell+
      D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
        ArithmeticFunction.cardFactors D.factorCount.factorial := by
  have hh := (genRank_le_strict_simple_add_actual_quotient D n ell hbelow hell hlt).trans
    (Nat.add_le_add_left (quotient_genRank_le_outer_multiplicity D) _)
  simpa only [Nat.add_assoc] using hh

theorem exists_generating_finset (n ell : ℕ)
    (hbelow : SmallerTransitiveRankBound n) (hell : LeastProperIndex D.Simple ell)
    (hlt : ell < n) :
    ∃ s : Finset G, Subgroup.closure (s : Set G) = ⊤ ∧
      s.card ≤ 2*traceyPermutationGeneratorCeiling ell+
        D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
          ArithmeticFunction.cardFactors D.factorCount.factorial := by
  obtain ⟨s,hs,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨s,hgen,hs.le.trans
    (genRank_le_strict_simple_add_outer_multiplicity D n ell hbelow hell hlt)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleStrictOuterOrdinaryRecurrence
