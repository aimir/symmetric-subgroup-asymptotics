import SymmetricSubgroupAsymptotics.OriginalFourPointSharedChooseCost
import SymmetricSubgroupAsymptotics.ActualWreathPrimeTopChiefOrdinaryBudget
import SymmetricSubgroupAsymptotics.EightPointFaithfulActionHalfDegreeReduction
import SymmetricSubgroupAsymptotics.OriginalTernaryBoundedSharpStep
import SymmetricSubgroupAsymptotics.SmallPrimeTopSharpFloorCertificates

/-! Actual affine four-point blocks below22 pay the sharp floor except
for the explicit coupled total-degree16 case or a precise small sporadic
failed action. At top3 the native odd kernel is split inside the SAME
source: zero odd image has only its dimension-two head, and nonzero odd
image shares that head in one position above the actual order-six tail.
No independent worst-case head/tail or new capacity premise is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalFourPointBoundedSharpStep
open OriginalBlockOrdinaryCompressionState OriginalAffineBlockCharacteristicHead
open EightPointHalfDegreeFiniteModelReduction TraceySharpHalfDegreeNumerics
open FiniteGroupPrimeMultiplicityGenerators

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by have h := block.degrees_ge_two.1; omega)
variable (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_sharpFloor_or_sixteen_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (hfour : Nat.card block.Fibre = 4) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ n = 16 ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  by_cases h16 : n = 16
  · exact Or.inr (Or.inl h16)
  have hproduct : 4*Nat.card block.Points = n := by
    simpa only [hfour,Nat.card_fin] using block.degree_product
  have ht2 := block.degrees_ge_two.2
  have ht5 : Nat.card block.Points ≤ 5 := by omega
  have hcases : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 ∨ Nat.card block.Points = 5 := by omega
  rcases hcases with ht | ht | ht
  · have hn : n = 8 := by omega
    rcases EightPointFaithfulActionHalfDegreeReduction.two_mul_genRank_le_card_or_sporadic_counterexample
      hCFSG (G := J) (X := Fin n)
      (by simpa only [Nat.card_fin,hn] using (show 8 ≤ 8 by decide))
      (by simpa only [Nat.card_fin,hn] using (show (8 : ℕ) ≠ 3 by decide)) with hpaid | hbad
    · have hg : MarkedC4.genRank J ≤ 4 := by simp only [Nat.card_fin] at hpaid; omega
      have hf8 : 4 ≤ sharpFloor 8 := TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square
        8 4 3 (by decide) (TinyPrimeTopSharpFloorNumerics.log_le_of_pow 8 3 (by decide) (by decide)) (by decide)
      exact Or.inl (hg.trans (by simpa only [hn] using hf8))
    · exact Or.inr (Or.inr (EightPointFaithfulActionHalfDegreeReduction.counterexample_mono (by decide : 8 ≤ 10) hbad))
  · have hn : n = 12 := by omega
    have hprime : (Fintype.card block.Points).Prime := by rw [Fintype.card_eq_nat_card,ht]; decide
    have htopcard : Nat.card block.Top ≤ 6 := by
      have hh := Nat.card_le_card_of_injective
        (MulAction.toPermHom block.Top block.Points) MulAction.toPerm_injective
      simpa only [Nat.card_perm,ht,Nat.factorial_succ,Nat.factorial_zero] using hh
    have htop : MarkedC4.genRank block.Top ≤ 2 := by
      by_contra hh
      have hg : 3 ≤ MarkedC4.genRank block.Top := by omega
      have hp := (Nat.pow_le_pow_right (by decide : 0 < 2) hg).trans
        ((FiniteGroupBinaryOrderGenerators.two_pow_genRank_le_card block.Top).trans htopcard)
      norm_num at hp
    have hdpos : 0 < translationDimension J block P :=
      (P.elementaryChart block.component_preprimitive).d_pos
    have hpow : P.p^translationDimension J block P = 4 :=
      (fibre_card_eq_prime_pow_dimension J block P).symm.trans hfour
    have hpdiv : P.p ∣ 2^2 := by
      change P.p ∣ 4
      rw [← hpow]
      exact dvd_pow_self _ hdpos.ne'
    have hp : P.p = 2 := Nat.prime_eq_prime_of_dvd_pow P.p_prime Nat.prime_two hpdiv
    have hd : translationDimension J block P = 2 := Nat.pow_right_injective (by decide : 2 ≤ 2)
      (by simpa only [hp] using hpow)
    have hg : MarkedC4.genRank J ≤ 5 := by
      by_cases hzero : BinaryPlaneWreathActualOddKernel.oddKernel
          (FourPointBlockAffineCoordinates.linearImage block.map block.map_equivariant block.base hfour) = ⊥
      · have hcapacity := ActualWreathPrimeTopChiefOrdinaryBudget.elementary_capacity_le_dimension
          (initialState J block) (QuotientGroup.mk' P.V) (translationChart J block P) block.base hprime
        change (headCharge J block P block.base).capacity ≤ translationDimension J block P at hcapacity
        have hgen := OriginalFourPointZeroOddCharacteristicCost.genRank_le_head_add_top
          J block P hfour hp hzero block.base
        omega
      · have horder := OriginalFourPointSharedChooseCost.quotientState_card_dvd_six J block P hp hd
        have hOmega : ArithmeticFunction.cardFactors (Nat.card (quotientState J block P).D) ≤ 2 :=
          (cardFactors_mono_of_dvd (Nat.card_pos (α := (quotientState J block P).D)).ne'
            (by decide : (6 : ℕ) ≠ 0) horder).trans_eq (by decide +kernel)
        have htail := ActualWreathPrimeTopChiefOrdinaryBudget.genRank_le_cardFactors_add_top
          (quotientState J block P) block.base hprime
        have hhead := OriginalFourPointSharedTranslationKernel.genRank_le_half_add_quotient
          J block P hfour hp hzero
        norm_num only [ht] at hhead
        omega
    exact Or.inl (hg.trans (by simpa only [hn] using TinyPrimeTopSharpFloorNumerics.five_le_sharpFloor_twelve))
  · have hn : n = 20 := by omega
    have hdiv : Nat.card block.Component ∣ 24 := by
      letI : Fintype block.Fibre := Fintype.ofFinite _
      have hh := Subgroup.card_dvd_of_injective block.Component.subtype block.Component.subtype_injective
      have he : Nat.card (Equiv.Perm block.Fibre) = 24 := by
        rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_eq_nat_card,hfour]
        norm_num
      simpa only [he] using hh
    have hOmega : ArithmeticFunction.cardFactors (Nat.card block.Component) ≤ 4 :=
      (cardFactors_mono_of_dvd (Nat.card_pos (α := block.Component)).ne'
        (by decide : (24 : ℕ) ≠ 0) hdiv).trans_eq (by decide +kernel)
    have hprime : (Fintype.card block.Points).Prime := by rw [Fintype.card_eq_nat_card,ht]; decide
    have hsource := ActualWreathPrimeTopChiefOrdinaryBudget.genRank_le_cardFactors_add_top
      (initialState J block) block.base hprime
    change MarkedC4.genRank J ≤ ArithmeticFunction.cardFactors (Nat.card block.Component) +
      MarkedC4.genRank block.Top at hsource
    rcases EightPointFaithfulActionHalfDegreeReduction.two_mul_genRank_le_card_or_sporadic_counterexample
      hCFSG (G := block.Top) (X := block.Points) (by omega) (by omega) with htop | hbad
    · have hg : MarkedC4.genRank J ≤ 6 := by omega
      exact Or.inl (hg.trans ((by decide : 6 ≤ 8).trans (by simpa only [hn] using
        SmallPrimeTopSharpFloorCertificates.eight_le_sharpFloor_twenty)))
    · exact Or.inr (Or.inr (EightPointFaithfulActionHalfDegreeReduction.counterexample_mono (by decide : 8 ≤ 10) hbad))

include P in
theorem exists_generating_finset_or_sixteen_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (hfour : Nat.card block.Fibre = 4) (hsmall : n < 22) :
    (∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n) ∨ n = 16 ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  rcases genRank_le_sharpFloor_or_sixteen_or_sporadic_counterexample J block P hCFSG hfour hsmall with hpaid | h16 | hbad
  · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨S,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr (Or.inl h16)
  · exact Or.inr (Or.inr hbad)

end SymmetricSubgroupAsymptotics.OriginalFourPointBoundedSharpStep
