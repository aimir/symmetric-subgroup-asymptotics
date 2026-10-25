import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorOrdinaryRecurrence
import Mathlib.Data.Finite.Perm

/-! The ACTUAL one-factor socle quotient divides both its genuine outer
group and the original faithful permutation-order quotient n!/|T|. Their
gcd pays its ordinary rank. In particular the full outer group is never
substituted for a smaller quotient that the same action cannot realize.
No model-order table, catalogue or permutation-generator input is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleActualQuotientGcdBudget
open PrimitiveSocleRawStructure FiniteGroupPrimeMultiplicityGenerators

section Normal
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]

theorem quotient_card_dvd_degree_factorial_div_normal (N : Subgroup G) [N.Normal] :
    Nat.card (G ⧸ N) ∣ (Nat.card X).factorial / Nat.card N := by
  have hG : Nat.card G ∣ (Nat.card X).factorial := by
    simpa only [Nat.card_perm] using Subgroup.card_dvd_of_injective
      (MulAction.toPermHom G X) MulAction.toPerm_injective
  have hprod : Nat.card N * Nat.card (G ⧸ N) = Nat.card G := by
    simpa only [N.index_eq_card] using N.card_mul_index
  have hN : Nat.card N ∣ (Nat.card X).factorial :=
    (show Nat.card N ∣ Nat.card G from ⟨Nat.card (G ⧸ N),hprod.symm⟩).trans hG
  have hmul : Nat.card N * Nat.card (G ⧸ N) ∣ (Nat.card X).factorial := by
    rw [hprod]
    exact hG
  apply (Nat.dvd_div_iff_mul_dvd hN).mpr
  simpa only [Nat.mul_comm] using hmul
end Normal

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X)

theorem quotient_card_dvd_degree_factorial_div_simple (hk : D.factorCount = 1) :
    Nat.card (G ⧸ finiteGroupSocle G) ∣ (Nat.card X).factorial / Nat.card D.Simple := by
  have hN : Nat.card (finiteGroupSocle G) = Nat.card D.Simple :=
    Nat.card_congr (D.oneFactorEquiv hk).toEquiv
  simpa only [hN] using
    (quotient_card_dvd_degree_factorial_div_normal (X := X) (finiteGroupSocle G))

theorem quotient_card_dvd_joint_order (hk : D.factorCount = 1) :
    Nat.card (G ⧸ finiteGroupSocle G) ∣
      (Nat.card (Outer D.Simple)).gcd ((Nat.card X).factorial / Nat.card D.Simple) := by
  have ho := PrimitiveSocleStrictOuterOrdinaryRecurrence.quotient_card_dvd_outer_wreath D
  simp only [hk,pow_one,Nat.factorial_one,mul_one] at ho
  exact Nat.dvd_gcd ho (quotient_card_dvd_degree_factorial_div_simple D hk)

theorem quotient_genRank_le_joint_cardFactors (hk : D.factorCount = 1) :
    MarkedC4.genRank (G ⧸ finiteGroupSocle G) ≤
      ArithmeticFunction.cardFactors ((Nat.card (Outer D.Simple)).gcd
        ((Nat.card X).factorial / Nat.card D.Simple)) := by
  have hp : 0 < (Nat.card (Outer D.Simple)).gcd
      ((Nat.card X).factorial / Nat.card D.Simple) :=
    Nat.gcd_pos_of_pos_left _ (Nat.card_pos (α := Outer D.Simple))
  exact (genRank_le_cardFactors (G ⧸ finiteGroupSocle G)).trans
    (cardFactors_mono_of_dvd (Nat.card_pos (α := G ⧸ finiteGroupSocle G)).ne' hp.ne'
      (quotient_card_dvd_joint_order D hk))

theorem genRank_le_simple_add_joint_cardFactors (hk : D.factorCount = 1) :
    MarkedC4.genRank G ≤ MarkedC4.genRank D.Simple +
      ArithmeticFunction.cardFactors ((Nat.card (Outer D.Simple)).gcd
        ((Nat.card X).factorial / Nat.card D.Simple)) :=
  (PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_actual_quotient D hk).trans
    (Nat.add_le_add_left (quotient_genRank_le_joint_cardFactors D hk) _)

theorem exists_generating_finset (hk : D.factorCount = 1) :
    ∃ F : Finset G, Subgroup.closure (F : Set G) = ⊤ ∧
      F.card ≤ MarkedC4.genRank D.Simple +
        ArithmeticFunction.cardFactors ((Nat.card (Outer D.Simple)).gcd
          ((Nat.card X).factorial / Nat.card D.Simple)) := by
  obtain ⟨F,hcard,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨F,hgen,hcard.le.trans (genRank_le_simple_add_joint_cardFactors D hk)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleActualQuotientGcdBudget
