import SymmetricSubgroupAsymptotics.ActualWreathPrimitiveSocleOrdinaryCompression
import SymmetricSubgroupAsymptotics.ActualWreathChiefUnitMinimumRate
import SymmetricSubgroupAsymptotics.PrimitiveSocleStrictOuterOrdinaryRecurrence

/-! The SAME actual remaining chief trace after local full-socle compression
is charged only to the genuine outer-wreath order. Both proved induced rates
are retained. The simple ordinary rank stays separate; no simple2generation,
Schreier solvability, permutation bound or scalar fitting premise is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathPrimitiveSocleOuterOrdinaryCost
open PrimitiveSocleRawStructure ActualWreathPrimitiveSocleOrdinaryCompression
open ActualWreathChiefUnitMinimumRate

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]
    (S : ActualWreathCompressionState Q I)
    {X : Type} [Finite X] [MulAction S.D X] (D : NonaffineData S.D X)

/-- The actual outer-wreath prime multiplicity, before any model estimate. -/
def outerMultiplicity : ℕ :=
  D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
    ArithmeticFunction.cardFactors D.factorCount.factorial

theorem quotient_cardFactors_le_outer_multiplicity :
    ArithmeticFunction.cardFactors (Nat.card (S.D ⧸ finiteGroupSocle S.D)) ≤
      outerMultiplicity S D := by
  have hh := FiniteGroupPrimeMultiplicityGenerators.cardFactors_mono_of_dvd
    (Nat.card_pos (α := S.D ⧸ finiteGroupSocle S.D)).ne'
    (mul_ne_zero (pow_ne_zero _ (Nat.card_pos (α := Outer D.Simple)).ne')
      (Nat.factorial_pos D.factorCount).ne')
    (PrimitiveSocleStrictOuterOrdinaryRecurrence.quotient_card_dvd_outer_wreath D)
  rw [ArithmeticFunction.cardFactors_mul
      (pow_ne_zero _ (Nat.card_pos (α := Outer D.Simple)).ne')
      (Nat.factorial_pos D.factorCount).ne',ArithmeticFunction.cardFactors_pow] at hh
  exact hh

/-- This estimates ANY chosen trace of the actual direct socle quotient. -/
theorem chiefCost_le_outer_multiplicity_rate {i : I} {n : ℕ}
    (h : ActualWreathOrdinaryChiefRecurrence.ChiefCost i (socleState S) n)
    (hI : 2 ≤ Fintype.card I) :
    (n : ℝ) ≤ (outerMultiplicity S D : ℝ)*rate (Fintype.card I) := by
  have hc := cost_le_cardFactors_mul_rate h hI
  change (n : ℝ) ≤
    (ArithmeticFunction.cardFactors (Nat.card (S.D ⧸ finiteGroupSocle S.D)) : ℝ)*
      rate (Fintype.card I) at hc
  have hOmega :
      (ArithmeticFunction.cardFactors (Nat.card (S.D ⧸ finiteGroupSocle S.D)) : ℝ) ≤
        outerMultiplicity S D := by
    exact_mod_cast quotient_cardFactors_le_outer_multiplicity S D
  exact hc.trans (mul_le_mul_of_nonneg_right hOmega
    (le_trans (by norm_num) (one_le_rate _ hI)))

theorem socle_quotient_genRank_le_outer_rate (i : I) (hI : 2 ≤ Fintype.card I) :
    (MarkedC4.genRank (socleState S).A : ℝ) ≤
      (outerMultiplicity S D : ℝ)*rate (Fintype.card I)+MarkedC4.genRank Q := by
  obtain ⟨n,hn⟩ := ActualWreathOrdinaryChiefRecurrence.exists_chiefCost i (socleState S)
  have hc := chiefCost_le_outer_multiplicity_rate S D hn hI
  have hs : (MarkedC4.genRank (socleState S).A : ℝ) ≤ (n : ℝ)+MarkedC4.genRank Q := by
    exact_mod_cast ActualWreathOrdinaryChiefRecurrence.genRank_le_cost_add_top hn
  exact hs.trans (add_le_add hc le_rfl)

variable [FaithfulSMul S.D X] [Nontrivial X] [MulAction.IsPreprimitive S.D X]

/-- The actual remaining trace and its outer-order charge are retained
alongside the genuine local simple-rank debt. -/
theorem exists_socle_trace_outer_cost (i : I) (hI : 2 ≤ Fintype.card I) :
    ∃ n : ℕ, ActualWreathOrdinaryChiefRecurrence.ChiefCost i (socleState S) n ∧
      (n : ℝ) ≤ (outerMultiplicity S D : ℝ)*rate (Fintype.card I) ∧
      MarkedC4.genRank S.A ≤ 2*MarkedC4.genRank D.Simple+n+MarkedC4.genRank Q := by
  obtain ⟨n,hn,hs⟩ := exists_socle_quotient_chiefCost S D i
  exact ⟨n,hn,chiefCost_le_outer_multiplicity_rate S D hn hI,hs⟩

theorem genRank_le_twice_simple_add_outer_rate (i : I) (hI : 2 ≤ Fintype.card I) :
    (MarkedC4.genRank S.A : ℝ) ≤ 2*(MarkedC4.genRank D.Simple : ℝ)+
      (outerMultiplicity S D : ℝ)*rate (Fintype.card I)+MarkedC4.genRank Q := by
  obtain ⟨n,hn,hc,hs⟩ := exists_socle_trace_outer_cost S D i hI
  have hsR : (MarkedC4.genRank S.A : ℝ) ≤
      2*(MarkedC4.genRank D.Simple : ℝ)+(n : ℝ)+MarkedC4.genRank Q := by
    exact_mod_cast hs
  linarith only [hsR,hc]

omit [FaithfulSMul S.D X] [Nontrivial X] [MulAction.IsPreprimitive S.D X] in
/-- The one-factor local socle pays exactly one rank debt, including t=2. -/
theorem genRank_le_simple_add_outer_rate_of_one_factor (i : I)
    (hI : 2 ≤ Fintype.card I) (hk : D.factorCount = 1) :
    (MarkedC4.genRank S.A : ℝ) ≤ (MarkedC4.genRank D.Simple : ℝ)+
      (outerMultiplicity S D : ℝ)*rate (Fintype.card I)+MarkedC4.genRank Q := by
  have hfirst : (MarkedC4.genRank S.A : ℝ) ≤
      (MarkedC4.genRank D.Simple : ℝ)+MarkedC4.genRank (socleState S).A := by
    exact_mod_cast genRank_le_simple_add_socle_quotient_of_one_factor S D hk
  have hnext := socle_quotient_genRank_le_outer_rate S D i hI
  linarith only [hfirst,hnext]

theorem exists_generating_finset (i : I) (hI : 2 ≤ Fintype.card I) :
    ∃ F : Finset S.A, Subgroup.closure (F : Set S.A) = ⊤ ∧
      (F.card : ℝ) ≤ 2*(MarkedC4.genRank D.Simple : ℝ)+
        (outerMultiplicity S D : ℝ)*rate (Fintype.card I)+MarkedC4.genRank Q := by
  obtain ⟨F,hcard,hgen⟩ := MarkedC4.genRank_spec (G := S.A)
  have hcardR : (F.card : ℝ) ≤ MarkedC4.genRank S.A := by exact_mod_cast hcard.le
  exact ⟨F,hgen,hcardR.trans (genRank_le_twice_simple_add_outer_rate S D i hI)⟩

end SymmetricSubgroupAsymptotics.ActualWreathPrimitiveSocleOuterOrdinaryCost
