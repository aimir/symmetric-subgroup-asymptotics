import SymmetricSubgroupAsymptotics.PrimitiveBoundedSharpElevenToTwentyOneCFSGReduction
import SymmetricSubgroupAsymptotics.CFSGPairedNonTypeAMinimumTwelve
import SymmetricSubgroupAsymptotics.CFSGTypeASmallDegreeOuterBudget
import SymmetricSubgroupAsymptotics.PrimitiveSocleSmallOuterOrdinaryBudgets

/-! Original nonaffine primitive sharp generation throughout degree6..10.
Actual paired models supply their proved pair internally. Literal proper
indices exclude B/C/D/Suzuki; the type-A/alternating outer budgets retain
the SAME quotient in the order360 case. Every other Lie model has actual
index at least24. Only actual Tits/sporadic factor data remain. There is
no induction, global Tracey/MN input, or finite action catalogue. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleSixToTenSharpCFSGReduction
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)

/-- A uniform integer/root comparison for this whole degree band. -/
theorem smallRank_le_sharpFloor (n : ℕ) (hlo : 6 ≤ n) (hhi : n ≤ 10) :
    (if n ≤ 7 then 3 else 4) ≤ sharpFloor n := by
  by_cases hs : n ≤ 7
  · rw [if_pos hs]
    exact TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square n 3 3 (by omega)
      (TinyPrimeTopSharpFloorNumerics.log_le_of_pow n 3 (by omega) (by norm_num; omega))
      (by have hh := Nat.pow_le_pow_left hlo 2; norm_num at hh ⊢; omega)
  rw [if_neg hs]
  by_cases h8 : n = 8
  · subst n
    exact TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square 8 4 3 (by decide)
      (TinyPrimeTopSharpFloorNumerics.log_le_of_pow 8 3 (by decide) (by decide)) (by decide)
  have hn9 : 9 ≤ n := by omega
  have hpow : (n : ℝ)^2 ≤ (2 : ℝ)^7 := by
    have hh := Nat.pow_le_pow_left hhi 2
    have hh' : n^2 ≤ 128 := by norm_num at hh ⊢; omega
    exact_mod_cast hh'
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (n : ℝ)^2) hpow
  simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hroot : Real.sqrt (Real.logb 2 (n : ℝ)) ≤ 15/8 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num,by linarith only [hl]⟩
  have hthree : (12/7 : ℝ) ≤ Real.sqrt 3 := Real.le_sqrt_of_sq_le (by norm_num)
  have hpos : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num)
    (by exact_mod_cast (show 1 < n by omega))
  have hnR : (9 : ℝ) ≤ n := by exact_mod_cast hn9
  have hproduct : (12/7 : ℝ)*9 ≤ Real.sqrt 3*(n : ℝ) :=
    mul_le_mul hthree hnR (by norm_num) (Real.sqrt_nonneg 3)
  apply Nat.le_floor
  apply (le_div_iff₀ (show 0 < 2*Real.sqrt (Real.logb 2 (n : ℝ)) by positivity)).mpr
  norm_num only [Nat.cast_ofNat]
  linarith only [hroot,hproduct]

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X)

theorem genRank_le_small_of_pair_family (j : CFSG.Index) (hj : PairFamily j)
    (e : D.Simple ≃* j.Model) (hlo : 6 ≤ Nat.card X) (hhi : Nat.card X ≤ 10) :
    MarkedC4.genRank G ≤ if Nat.card X ≤ 7 then 3 else 4 := by
  classical
  letI : Finite j.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup j.Model := e.symm.isSimpleGroup
  have hn : ¬ IsMulCommutative j.Model := by
    intro hh
    exact D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr hh)
  have hpacket : CFSGReduction.ModelSufficientSimpleIndexBounds j := by
    rcases CFSGSimpleIndexPacketOrTitsSporadic.model_packet_or_remaining j hn with hp | hm
    · exact hp
    · have hnot : ¬ RemainingModel j := by
        cases j <;> simp_all only [PairFamily,RemainingModel]
      exact (hnot hm).elim
  obtain ⟨S,hS,hcard⟩ := OriginalNonaffineSmallPairFamiliesBlockOrdinaryStep.model_pair_of_family j hj
  have hhead : MarkedC4.genRank D.Simple ≤ 2 := by
    rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e]
    exact (MarkedC4.genRank_le hS).trans hcard
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hellM := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  have hm := hpacket ell hellM
  have horder : ell^2 < Nat.card D.Simple := by
    simpa only [Nat.card_congr e.toEquiv] using hm.1
  have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
    rw [CFSGReduction.outer_card_congr e]
    exact hm.2
  have hk := (PrimitiveSocleDegreeBelowTwentyFiveOuterMultiplicity.factor_and_outer_multiplicity
    D (by omega) ell hell horder houter).1
  have hedegree := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hthree : 3 ≤ if Nat.card X ≤ 7 then 3 else 4 := by split_ifs <;> decide
  cases j with
  | alternating m hms =>
      by_cases hs : Nat.card X ≤ 7
      · have hg := PrimitiveSocleSmallOuterOrdinaryBudgets.genRank_le_three_of_alternating
          D hk (by omega) hhead m hms e
        simpa only [if_pos hs] using hg
      · have ho : Nat.card (Outer D.Simple) ≤ 4 := by
          rw [CFSGReduction.outer_card_congr e]
          exact CFSGAlternatingOuterBound.outer_card_le_four m hms
        have hg := PrimitiveSocleSmallOuterOrdinaryBudgets.genRank_le_four_of_outer_le_four D hk hhead ho
        simpa only [if_neg hs] using hg
  | A r q hr hs =>
      letI : IsSimpleGroup (CFSG.Models.A r q) := e.symm.isSimpleGroup
      by_cases h1 : r = 1
      · subst r
        by_cases hn7 : Nat.card X ≤ 7
        · rcases CFSGTypeASmallDegreeOuterBudget.rank_one_outer_le_two_or_order_three_sixty
            q ell hellM (by omega) with ho | ⟨hT,ho⟩
          · have hactual : Nat.card (Outer D.Simple) ≤ 2 := by
              simpa only [CFSGReduction.outer_card_congr e] using ho
            have hg := PrimitiveSocleSmallOuterOrdinaryBudgets.genRank_le_three_of_outer_le_two
              D hk hhead hactual
            simpa only [if_pos hn7] using hg
          · have hactual : Nat.card (Outer D.Simple) ≤ 4 := by
              simpa only [CFSGReduction.outer_card_congr e] using ho
            have hTactual : Nat.card D.Simple = 360 := (Nat.card_congr e.toEquiv).trans hT
            have hg := PrimitiveSocleOrderThreeSixtySmallQuotient.genRank_le_three
              D hk (by omega) hTactual hactual hhead
            simpa only [if_pos hn7] using hg
        · have ho := CFSGTypeASmallDegreeOuterBudget.rank_one_outer_card_le_four
            q ell hellM (by omega)
          have hactual : Nat.card (Outer D.Simple) ≤ 4 := by
            simpa only [CFSGReduction.outer_card_congr e] using ho
          have hg := PrimitiveSocleSmallOuterOrdinaryBudgets.genRank_le_four_of_outer_le_four D hk hhead hactual
          simpa only [if_neg hn7] using hg
      · have ho := CFSGTypeASmallDegreeOuterBudget.higher_outer_card_le_two r (by omega)
          q ell hellM (by omega)
        have hactual : Nat.card (Outer D.Simple) ≤ 2 := by
          simpa only [CFSGReduction.outer_card_congr e] using ho
        exact (PrimitiveSocleSmallOuterOrdinaryBudgets.genRank_le_three_of_outer_le_two
          D hk hhead hactual).trans hthree
  | B r q hr =>
      letI : IsSimpleGroup (CFSG.Models.B r q) := e.symm.isSimpleGroup
      have hh := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 12
        (CFSGPairedNonTypeAMinimumTwelve.typeB r hr q)
      omega
  | C r q hr hs =>
      letI : IsSimpleGroup (CFSG.Models.C r q) := e.symm.isSimpleGroup
      have hh := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 12
        (CFSGPairedNonTypeAMinimumTwelve.typeC r hr q hs)
      omega
  | D r q hr =>
      letI : IsSimpleGroup (CFSG.Models.D r q) := e.symm.isSimpleGroup
      have hh := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 12
        (CFSGPairedNonTypeAMinimumTwelve.typeD r hr q)
      omega
  | suzuki m hmPositive =>
      letI : IsSimpleGroup (CFSG.Models.Suzuki m) := e.symm.isSimpleGroup
      have hh := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 12
        (CFSGPairedNonTypeAMinimumTwelve.suzuki m hmPositive)
      omega
  | cyclic p hp => exact hj.elim
  | twistedA r q hr hs => exact hj.elim
  | twistedD r q hr => exact hj.elim
  | F4 q => exact hj.elim
  | G2 q hs => exact hj.elim
  | E6 q => exact hj.elim
  | E7 q => exact hj.elim
  | E8 q => exact hj.elim
  | twistedE6 q => exact hj.elim
  | trialityD4 q => exact hj.elim
  | reeG2 m hm => exact hj.elim
  | reeF4 m hm => exact hj.elim
  | tits => exact hj.elim
  | sporadic s => exact hj.elim

theorem genRank_le_sharpFloor_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (hlo : 6 ≤ Nat.card X) (hhi : Nat.card X ≤ 10) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases PrimitiveSocleNonpairDegreeTwentyFour.pair_family_or_actual_remaining_of_degree_below_twenty_four
    D hCFSG (by omega) with ⟨j,hj,⟨e⟩⟩ | hm
  · exact Or.inl ((genRank_le_small_of_pair_family D j hj e hlo hhi).trans
      (smallRank_le_sharpFloor (Nat.card X) hlo hhi))
  · exact Or.inr hm

theorem exists_generating_finset_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (hlo : 6 ≤ Nat.card X) (hhi : Nat.card X ≤ 10) :
    (∃ F : Finset G, Subgroup.closure (F : Set G) = ⊤ ∧ F.card ≤ sharpFloor (Nat.card X)) ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases genRank_le_sharpFloor_or_actual_remaining_model D hCFSG hlo hhi with hg | hm
  · obtain ⟨F,hcard,hgen⟩ := MarkedC4.genRank_spec (G := G)
    exact Or.inl ⟨F,hgen,hcard.le.trans hg⟩
  · exact Or.inr hm

end SymmetricSubgroupAsymptotics.PrimitiveSocleSixToTenSharpCFSGReduction
