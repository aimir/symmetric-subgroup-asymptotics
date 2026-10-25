import SymmetricSubgroupAsymptotics.ActualWreathPrimeTopChiefOrdinaryBudget
import SymmetricSubgroupAsymptotics.ActualWreathPrimitiveSocleOuterOrdinaryCost

/-! A prime number of actual blocks makes the entire SAME socle-quotient
chief trace cost at most its literal outer prime multiplicity. The original
correlated source and original top are retained. One or two genuine local
simple ordinary ranks pay the actual full socle; no two-generation or
permutation-generator theorem is an input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathPrimeTopSocleOrdinaryCost
open PrimitiveSocleRawStructure ActualWreathPrimitiveSocleOrdinaryCompression
open ActualWreathPrimitiveSocleOuterOrdinaryCost

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]
    (S : ActualWreathCompressionState Q I)
    {X : Type} [Finite X] [MulAction S.D X] (D : NonaffineData S.D X)

theorem socle_quotient_genRank_le_outer_add_top (i : I)
    (hprime : (Fintype.card I).Prime) :
    MarkedC4.genRank (socleState S).A ≤ outerMultiplicity S D + MarkedC4.genRank Q := by
  have hh := ActualWreathPrimeTopChiefOrdinaryBudget.genRank_le_cardFactors_add_top
    (socleState S) i hprime
  change MarkedC4.genRank (socleState S).A ≤
    ArithmeticFunction.cardFactors (Nat.card (S.D ⧸ finiteGroupSocle S.D)) +
      MarkedC4.genRank Q at hh
  exact hh.trans (Nat.add_le_add_right (quotient_cardFactors_le_outer_multiplicity S D) _)

theorem genRank_le_simple_add_outer_add_top_of_one_factor (i : I)
    (hprime : (Fintype.card I).Prime) (hk : D.factorCount = 1) :
    MarkedC4.genRank S.A ≤ MarkedC4.genRank D.Simple +
      ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) + MarkedC4.genRank Q := by
  have hs := genRank_le_simple_add_socle_quotient_of_one_factor S D hk
  have hq := socle_quotient_genRank_le_outer_add_top S D i hprime
  have ho : outerMultiplicity S D =
      ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) := by
    simp only [outerMultiplicity,hk,one_mul,Nat.factorial_one,
      ArithmeticFunction.cardFactors_one,add_zero]
  rw [ho] at hq
  omega

variable [FaithfulSMul S.D X] [Nontrivial X] [MulAction.IsPreprimitive S.D X]

theorem genRank_le_twice_simple_add_outer_add_top (i : I)
    (hprime : (Fintype.card I).Prime) :
    MarkedC4.genRank S.A ≤ 2 * MarkedC4.genRank D.Simple +
      outerMultiplicity S D + MarkedC4.genRank Q := by
  have hs := genRank_le_twice_simple_add_socle_quotient S D
  have hq := socle_quotient_genRank_le_outer_add_top S D i hprime
  omega

theorem exists_generating_finset (i : I) (hprime : (Fintype.card I).Prime) :
    ∃ F : Finset S.A, Subgroup.closure (F : Set S.A) = ⊤ ∧
      F.card ≤ 2 * MarkedC4.genRank D.Simple + outerMultiplicity S D + MarkedC4.genRank Q := by
  obtain ⟨F,hcard,hgen⟩ := MarkedC4.genRank_spec (G := S.A)
  exact ⟨F,hgen,hcard.le.trans (genRank_le_twice_simple_add_outer_add_top S D i hprime)⟩

end SymmetricSubgroupAsymptotics.ActualWreathPrimeTopSocleOrdinaryCost
