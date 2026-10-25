import SymmetricSubgroupAsymptotics.OriginalTernaryCoarseOrdinaryStep
import SymmetricSubgroupAsymptotics.ActualWreathPrimeTopChiefOrdinaryBudget
import SymmetricSubgroupAsymptotics.ActualWreathSixTopChiefOrdinaryBudget
import SymmetricSubgroupAsymptotics.EightPointFaithfulActionHalfDegreeReduction
import SymmetricSubgroupAsymptotics.PrimitiveAffineNineOrdinaryGenerators
import SymmetricSubgroupAsymptotics.TinyPrimeTopSharpFloorNumerics

/-! All original three-point minimal-block actions below22 pay the
literal sharp floor, or yield the precise bounded sporadic failed-action
record from the actual top action. Prime tops retain the same chief trace;
tops4 and6 use actual mixed-characteristic exact-divisor capacities.
There is no global MN/Tracey or supplied local capacity assumption. The
sporadic witness is global and is not asserted to be a subquotient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalTernaryBoundedSharpStep
open OriginalBlockOrdinaryCompressionState TraceySharpHalfDegreeNumerics
open ActualWreathChooseDivisorCapacity EightPointHalfDegreeFiniteModelReduction
open FiniteGroupPrimeMultiplicityGenerators

theorem three_le_sharpFloor_six : 3 ≤ sharpFloor 6 :=
  TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square 6 3 3 (by decide)
    (TinyPrimeTopSharpFloorNumerics.log_le_of_pow 6 3 (by decide) (by decide)) (by decide)

theorem seven_le_sharpFloor_eighteen : 7 ≤ sharpFloor 18 := by
  have hp : (18 : ℝ)^2 ≤ (2 : ℝ)^9 := by norm_num
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < (18 : ℝ)^2) hp
  simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hlog : Real.logb 2 (18 : ℝ) ≤ 9/2 := by linarith only [hl]
  have hroot : Real.sqrt (Real.logb 2 (18 : ℝ)) ≤ 15/7 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num,by linarith only [hlog]⟩
  have hthree : (12/7 : ℝ) ≤ Real.sqrt 3 := Real.le_sqrt_of_sq_le (by norm_num)
  have hpos : 0 < Real.logb 2 (18 : ℝ) := Real.logb_pos (by norm_num) (by norm_num)
  apply Nat.le_floor
  apply (le_div_iff₀ (show 0 < 2*Real.sqrt (Real.logb 2 (18 : ℝ)) by positivity)).mpr
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hroot,hthree]

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

private theorem top_rank_or_sporadic_counterexample (hCFSG : CFSG.CFSGClassification)
    (ht : Nat.card block.Points ≤ 7) :
    MarkedC4.genRank block.Top ≤ Nat.card block.Points/2 +
      (if Nat.card block.Points = 3 then 1 else 0) ∨
        Nonempty (PrimitiveSporadicCounterexample 8) := by
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
  · rcases EightPointFaithfulActionHalfDegreeReduction.two_mul_genRank_le_card_or_sporadic_counterexample
      hCFSG (G := block.Top) (X := block.Points) (by omega) hthree with hp | hbad
    · exact Or.inl (by simp only [if_neg hthree]; omega)
    · exact Or.inr hbad

theorem genRank_le_sharpFloor_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (hr : Nat.card block.Fibre = 3) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ Nonempty (PrimitiveSporadicCounterexample 8) := by
  have hproduct : 3*Nat.card block.Points = n := by
    simpa only [hr,Nat.card_fin] using block.degree_product
  have ht2 := block.degrees_ge_two.2
  have ht7 : Nat.card block.Points ≤ 7 := by omega
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using ht2
  have horder := OriginalTernaryCoarseOrdinaryStep.component_card_dvd_six J block hr
  have hOmega : ArithmeticFunction.cardFactors (Nat.card block.Component) ≤ 2 :=
    (cardFactors_mono_of_dvd (Nat.card_pos (α := block.Component)).ne'
      (by decide : (6 : ℕ) ≠ 0) horder).trans_eq (by decide +kernel)
  rcases top_rank_or_sporadic_counterexample J block hCFSG ht7 with htop | hbad
  swap
  · exact Or.inr hbad
  apply Or.inl
  by_cases ht4 : Nat.card block.Points = 4
  · have hdiv : 2^2 ∣ Fintype.card block.Points := by
      norm_num only [Fintype.card_eq_nat_card,ht4]
    have hh := ActualWreathSixOrderChooseCost.genRank_le_primary_choose_add_primeTo
      (initialState J block) block.base hI horder 2 hdiv
    change (MarkedC4.genRank J : ℝ) ≤ _ + _ + MarkedC4.genRank block.Top at hh
    norm_num only [Fintype.card_eq_nat_card,ht4,primaryRate,Nat.choose,min_def] at hh
    have htopN : MarkedC4.genRank block.Top ≤ 2 := by
      have hh := htop
      norm_num only [ht4] at hh
      exact hh
    have htopR : (MarkedC4.genRank block.Top : ℝ) ≤ 2 := by exact_mod_cast htopN
    have hg : MarkedC4.genRank J ≤ 5 := by exact_mod_cast (show (MarkedC4.genRank J : ℝ) ≤ 5 by linarith)
    have hn : n = 12 := by omega
    exact hg.trans (by simpa only [hn] using TinyPrimeTopSharpFloorNumerics.five_le_sharpFloor_twelve)
  by_cases ht6 : Nat.card block.Points = 6
  · have htF : Fintype.card block.Points = 6 := by
      simpa only [Fintype.card_eq_nat_card] using ht6
    have hh := ActualWreathSixTopChiefOrdinaryBudget.genRank_le_four_add_top_of_card_dvd_six
      (initialState J block) block.base htF horder
    change MarkedC4.genRank J ≤ 4+MarkedC4.genRank block.Top at hh
    have htopN : MarkedC4.genRank block.Top ≤ 3 := by
      have h := htop
      norm_num only [ht6] at h
      exact h
    have hg : MarkedC4.genRank J ≤ 7 := by omega
    have hn : n = 18 := by omega
    exact hg.trans (by simpa only [hn] using seven_le_sharpFloor_eighteen)
  have hcases : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 ∨
      Nat.card block.Points = 5 ∨ Nat.card block.Points = 7 := by omega
  have hprime : (Fintype.card block.Points).Prime := by
    rw [Fintype.card_eq_nat_card]
    rcases hcases with ht | ht | ht | ht <;> rw [ht] <;> decide
  have hh := ActualWreathPrimeTopChiefOrdinaryBudget.genRank_le_cardFactors_add_top
    (initialState J block) block.base hprime
  change MarkedC4.genRank J ≤ ArithmeticFunction.cardFactors (Nat.card block.Component) +
    MarkedC4.genRank block.Top at hh
  rcases hcases with ht | ht | ht | ht
  · have htopN : MarkedC4.genRank block.Top ≤ 1 := by
      have hh := htop
      norm_num only [ht] at hh
      exact hh
    have hg : MarkedC4.genRank J ≤ 3 := by omega
    have hn : n = 6 := by omega
    exact hg.trans (by simpa only [hn] using three_le_sharpFloor_six)
  · have htopN : MarkedC4.genRank block.Top ≤ 2 := by
      have hh := htop
      norm_num only [ht] at hh
      exact hh
    have hg : MarkedC4.genRank J ≤ 4 := by omega
    have hn : n = 9 := by omega
    exact hg.trans (by simpa only [hn] using PrimitiveAffineNineOrdinaryGenerators.four_le_sharpFloor_nine)
  · have htopN : MarkedC4.genRank block.Top ≤ 2 := by
      have hh := htop
      norm_num only [ht] at hh
      exact hh
    have hg : MarkedC4.genRank J ≤ 4 := by omega
    have hn : n = 15 := by omega
    exact hg.trans ((by decide : 4 ≤ 6).trans (by simpa only [hn] using
      TinyPrimeTopSharpFloorNumerics.six_le_sharpFloor_fifteen))
  · have htopN : MarkedC4.genRank block.Top ≤ 3 := by
      have hh := htop
      norm_num only [ht] at hh
      exact hh
    have hg : MarkedC4.genRank J ≤ 5 := by omega
    have hn : n = 21 := by omega
    exact hg.trans ((by decide : 5 ≤ 8).trans (by simpa only [hn] using
      TinyPrimeTopSharpFloorNumerics.eight_le_sharpFloor_twenty_one))

theorem exists_generating_finset_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (hr : Nat.card block.Fibre = 3) (hsmall : n < 22) :
    (∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n) ∨
      Nonempty (PrimitiveSporadicCounterexample 8) := by
  rcases genRank_le_sharpFloor_or_sporadic_counterexample J block hCFSG hr hsmall with hpaid | hbad
  · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨S,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr hbad

end SymmetricSubgroupAsymptotics.OriginalTernaryBoundedSharpStep
