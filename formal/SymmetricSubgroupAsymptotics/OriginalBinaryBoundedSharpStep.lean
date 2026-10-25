import SymmetricSubgroupAsymptotics.TenPointHalfDegreeFiniteModelReduction
import SymmetricSubgroupAsymptotics.ActualWreathPrimeOrderCoprimeDivisorBudget
import SymmetricSubgroupAsymptotics.ActualWreathSharpUniformLocalOrderCost
import SymmetricSubgroupAsymptotics.OriginalTernaryBoundedSharpStep
import SymmetricSubgroupAsymptotics.OriginalNonaffineBoundedSharpCFSGReduction

/-! All actual two-point minimal-block actions below22 pay the literal
sharp floor, apart from the explicit total-degree16 coupled case or an
actual bounded sporadic failed action. Tops6/9/10 retain their coprime
prime-power capacities on the SAME local chief trace. No current-degree
induction, supplied top bound, or global permutation input occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryBoundedSharpStep
open OriginalBlockOrdinaryCompressionState TraceySharpHalfDegreeNumerics
open EightPointHalfDegreeFiniteModelReduction FiniteGroupPrimeMultiplicityGenerators

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

private theorem component_card_dvd_two (hr : Nat.card block.Fibre = 2) :
    Nat.card block.Component ∣ 2 := by
  letI : Fintype block.Fibre := Fintype.ofFinite _
  have hd := Subgroup.card_dvd_of_injective block.Component.subtype block.Component.subtype_injective
  have hperm : Nat.card (Equiv.Perm block.Fibre) = 2 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_eq_nat_card,hr]
    norm_num
  simpa only [hperm] using hd

private theorem top_rank_or_sporadic_counterexample (hCFSG : CFSG.CFSGClassification)
    (ht : Nat.card block.Points ≤ 10) :
    MarkedC4.genRank block.Top ≤ Nat.card block.Points/2 +
      (if Nat.card block.Points = 3 then 1 else 0) ∨
        Nonempty (PrimitiveSporadicCounterexample 10) := by
  by_cases hthree : Nat.card block.Points = 3
  · have hcard : Nat.card block.Top ≤ 6 := by
      have hh := Nat.card_le_card_of_injective
        (MulAction.toPermHom block.Top block.Points) MulAction.toPerm_injective
      simpa only [Nat.card_perm,hthree,Nat.factorial_succ,Nat.factorial_zero] using hh
    have htop : MarkedC4.genRank block.Top ≤ 2 := by
      by_contra hh
      have hg : 3 ≤ MarkedC4.genRank block.Top := by omega
      have hp := (Nat.pow_le_pow_right (by decide : 0 < 2) hg).trans
        ((FiniteGroupBinaryOrderGenerators.two_pow_genRank_le_card block.Top).trans hcard)
      norm_num at hp
    exact Or.inl (by norm_num only [hthree]; exact htop)
  · rcases TenPointHalfDegreeFiniteModelReduction.two_mul_genRank_le_card_or_sporadic_counterexample
      hCFSG (G := block.Top) (X := block.Points) ht hthree with hp | hbad
    · exact Or.inl (by simp only [if_neg hthree]; omega)
    · exact Or.inr hbad

theorem genRank_le_sharpFloor_or_sixteen_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (hr : Nat.card block.Fibre = 2) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ n = 16 ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  by_cases h16 : n = 16
  · exact Or.inr (Or.inl h16)
  have hproduct : 2*Nat.card block.Points = n := by
    simpa only [hr,Nat.card_fin] using block.degree_product
  have ht2 := block.degrees_ge_two.2
  have ht10 : Nat.card block.Points ≤ 10 := by omega
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using ht2
  have horder := component_card_dvd_two J block hr
  have hOmega : ArithmeticFunction.cardFactors (Nat.card block.Component) ≤ 1 :=
    (cardFactors_mono_of_dvd (Nat.card_pos (α := block.Component)).ne'
      (by decide : (2 : ℕ) ≠ 0) horder).trans_eq (by decide +kernel)
  have hbase := ActualWreathSharpUniformLocalOrderCost.genRank_le_half_local_cardFactors
    (initialState J block) block.base hI
  change (MarkedC4.genRank J : ℝ) ≤
    (ArithmeticFunction.cardFactors (Nat.card block.Component) : ℝ)*(Fintype.card block.Points : ℝ)/2+
      MarkedC4.genRank block.Top at hbase
  have hm : (ArithmeticFunction.cardFactors (Nat.card block.Component) : ℝ)*
      ((Fintype.card block.Points : ℝ)/2) ≤ (Fintype.card block.Points : ℝ)/2 := by
    have hh := mul_le_mul_of_nonneg_right
      (show (ArithmeticFunction.cardFactors (Nat.card block.Component) : ℝ) ≤ 1 by exact_mod_cast hOmega)
      (show (0 : ℝ) ≤ (Fintype.card block.Points : ℝ)/2 by positivity)
    simpa only [one_mul] using hh
  have hhalf : MarkedC4.genRank J ≤ Nat.card block.Points/2+MarkedC4.genRank block.Top := by
    have hhR : (2 : ℝ)*MarkedC4.genRank J ≤
        (Fintype.card block.Points : ℝ)+2*MarkedC4.genRank block.Top := by linarith only [hbase,hm]
    have hhR' : (2 : ℝ)*MarkedC4.genRank J ≤
        (Nat.card block.Points : ℝ)+2*MarkedC4.genRank block.Top := by
      simpa only [Fintype.card_eq_nat_card] using hhR
    have hhN : 2*MarkedC4.genRank J ≤ Nat.card block.Points+2*MarkedC4.genRank block.Top := by
      exact_mod_cast hhR'
    omega
  rcases top_rank_or_sporadic_counterexample J block hCFSG ht10 with htop | hbad
  swap
  · exact Or.inr (Or.inr hbad)
  apply Or.inl
  by_cases hspecial : Nat.card block.Points = 6 ∨ Nat.card block.Points = 9 ∨ Nat.card block.Points = 10
  · rcases hspecial with ht | ht | ht
    · have hd : 3^1 ∣ Fintype.card block.Points := by norm_num only [Fintype.card_eq_nat_card,ht]
      have hh := ActualWreathPrimeOrderCoprimeDivisorBudget.genRank_le_primeTo_divisor_add_top
        (initialState J block) block.base hI 2 3 1 Nat.prime_two Nat.prime_three (by decide) horder hd
      change (MarkedC4.genRank J : ℝ) ≤ _+MarkedC4.genRank block.Top at hh
      norm_num only [Fintype.card_eq_nat_card,ht] at hh
      have htopN : MarkedC4.genRank block.Top ≤ 3 := by
        have h := htop; norm_num only [ht] at h; exact h
      have htopR : (MarkedC4.genRank block.Top : ℝ) ≤ 3 := by exact_mod_cast htopN
      have hg : MarkedC4.genRank J ≤ 5 := by exact_mod_cast (show (MarkedC4.genRank J : ℝ) ≤ 5 by linarith)
      have hn : n = 12 := by omega
      exact hg.trans (by simpa only [hn] using TinyPrimeTopSharpFloorNumerics.five_le_sharpFloor_twelve)
    · have hd : 3^2 ∣ Fintype.card block.Points := by norm_num only [Fintype.card_eq_nat_card,ht]
      have hh := ActualWreathPrimeOrderCoprimeDivisorBudget.genRank_le_primeTo_divisor_add_top
        (initialState J block) block.base hI 2 3 2 Nat.prime_two Nat.prime_three (by decide) horder hd
      change (MarkedC4.genRank J : ℝ) ≤ _+MarkedC4.genRank block.Top at hh
      norm_num only [Fintype.card_eq_nat_card,ht] at hh
      have htopN : MarkedC4.genRank block.Top ≤ 4 := by
        have h := htop; norm_num only [ht] at h; exact h
      have htopR : (MarkedC4.genRank block.Top : ℝ) ≤ 4 := by exact_mod_cast htopN
      have hg : MarkedC4.genRank J ≤ 5 := by exact_mod_cast (show (MarkedC4.genRank J : ℝ) ≤ 5 by linarith)
      have hn : n = 18 := by omega
      exact hg.trans ((by decide : 5 ≤ 7).trans (by simpa only [hn] using
        OriginalTernaryBoundedSharpStep.seven_le_sharpFloor_eighteen))
    · have hd : 5^1 ∣ Fintype.card block.Points := by norm_num only [Fintype.card_eq_nat_card,ht]
      have hh := ActualWreathPrimeOrderCoprimeDivisorBudget.genRank_le_primeTo_divisor_add_top
        (initialState J block) block.base hI 2 5 1 Nat.prime_two (by decide) (by decide) horder hd
      change (MarkedC4.genRank J : ℝ) ≤ _+MarkedC4.genRank block.Top at hh
      norm_num only [Fintype.card_eq_nat_card,ht] at hh
      have htopN : MarkedC4.genRank block.Top ≤ 5 := by
        have h := htop; norm_num only [ht] at h; exact h
      have htopR : (MarkedC4.genRank block.Top : ℝ) ≤ 5 := by exact_mod_cast htopN
      have hg : MarkedC4.genRank J ≤ 7 := by exact_mod_cast (show (MarkedC4.genRank J : ℝ) ≤ 7 by linarith)
      have hn : n = 20 := by omega
      exact hg.trans ((by decide : 7 ≤ 8).trans (by simpa only [hn] using
        SmallPrimeTopSharpFloorCertificates.eight_le_sharpFloor_twenty))
  have hcases : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 ∨
      Nat.card block.Points = 4 ∨ Nat.card block.Points = 5 ∨ Nat.card block.Points = 7 := by omega
  rcases hcases with ht | ht | ht | ht | ht
  · have hg : MarkedC4.genRank J ≤ 2 := by norm_num only [ht,if_true,if_false] at hhalf htop; omega
    have hn : n = 4 := by omega
    exact hg.trans (by simpa only [hn] using PrimitiveBoundedSharpCFSGReduction.two_le_sharpFloor_four)
  · have hg : MarkedC4.genRank J ≤ 3 := by norm_num only [ht,if_true,if_false] at hhalf htop; omega
    have hn : n = 6 := by omega
    exact hg.trans (by simpa only [hn] using OriginalTernaryBoundedSharpStep.three_le_sharpFloor_six)
  · have hg : MarkedC4.genRank J ≤ 4 := by norm_num only [ht,if_true,if_false] at hhalf htop; omega
    have hn : n = 8 := by omega
    have hf8 : 4 ≤ sharpFloor 8 := TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square
      8 4 3 (by decide) (TinyPrimeTopSharpFloorNumerics.log_le_of_pow 8 3 (by decide) (by decide)) (by decide)
    exact hg.trans (by simpa only [hn] using hf8)
  · have hg : MarkedC4.genRank J ≤ 4 := by norm_num only [ht,if_true,if_false] at hhalf htop; omega
    have hn : n = 10 := by omega
    exact hg.trans (by simpa only [hn] using SmallPrimeTopSharpFloorCertificates.four_le_sharpFloor_ten)
  · have hg : MarkedC4.genRank J ≤ 6 := by norm_num only [ht,if_true,if_false] at hhalf htop; omega
    have hn : n = 14 := by omega
    exact hg.trans (OriginalNonaffineBoundedSharpCFSGReduction.six_le_sharpFloor_of_band n (by omega) (by omega))

theorem exists_generating_finset_or_sixteen_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (hr : Nat.card block.Fibre = 2) (hsmall : n < 22) :
    (∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n) ∨ n = 16 ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  rcases genRank_le_sharpFloor_or_sixteen_or_sporadic_counterexample J block hCFSG hr hsmall with hpaid | h16 | hbad
  · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨S,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr (Or.inl h16)
  · exact Or.inr (Or.inr hbad)

end SymmetricSubgroupAsymptotics.OriginalBinaryBoundedSharpStep
