import SymmetricSubgroupAsymptotics.PrimitiveSocleSmallOuterOrdinaryBudgets

/-! The SAME actual quotient cannot have order four when its simple
socle has order divisible by four and the original group has order not
divisible by sixteen. Its genuine ordinary rank is then at most one.
A displayed pair for the simple factor therefore gives three original
generators, without charging the full outer group as the quotient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleFourDivisorOuterFourOrdinary
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_three (hk : D.factorCount = 1)
    (hhead : MarkedC4.genRank D.Simple ≤ 2)
    (houter : Nat.card (Outer D.Simple) ≤ 4)
    (hfour : 4 ∣ Nat.card D.Simple) (hnotSixteen : ¬ 16 ∣ Nat.card G) :
    MarkedC4.genRank G ≤ 3 := by
  let Q := G ⧸ finiteGroupSocle G
  have hdiv : Nat.card Q ∣ Nat.card (Outer D.Simple) := by
    have h := PrimitiveSocleStrictOuterOrdinaryRecurrence.quotient_card_dvd_outer_wreath D
    simpa only [hk,pow_one,Nat.factorial_one,mul_one] using h
  have hq : Nat.card Q ≤ 4 :=
    (Nat.le_of_dvd (Nat.card_pos (α := Outer D.Simple)) hdiv).trans houter
  have hN : Nat.card (finiteGroupSocle G) = Nat.card D.Simple :=
    Nat.card_congr (D.oneFactorEquiv hk).toEquiv
  have hG : Nat.card G = Nat.card D.Simple * Nat.card Q := by
    have h := (finiteGroupSocle G).card_mul_index
    rw [(finiteGroupSocle G).index_eq_card,hN] at h
    exact h.symm
  have hne : Nat.card Q ≠ 4 := by
    intro h
    apply hnotSixteen
    rw [hG,h]
    simpa only [show 4*4=16 by decide] using Nat.mul_dvd_mul hfour (dvd_refl 4)
  have homega : ArithmeticFunction.cardFactors (Nat.card Q) ≤ 1 :=
    SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow
      (Nat.card Q) 1 (Nat.card_pos (α := Q)) (by norm_num; omega)
  have hqr : MarkedC4.genRank Q ≤ 1 :=
    (FiniteGroupPrimeMultiplicityGenerators.genRank_le_cardFactors Q).trans homega
  have hrec := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_actual_quotient D hk
  change MarkedC4.genRank G ≤ MarkedC4.genRank D.Simple + MarkedC4.genRank Q at hrec
  omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleFourDivisorOuterFourOrdinary
