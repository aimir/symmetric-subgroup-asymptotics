import SymmetricSubgroupAsymptotics.PrimitiveSocleSixToTenSharpCFSGReduction
import SymmetricSubgroupAsymptotics.CFSGTypeARankOneDegreeEightOuterAlternative
import SymmetricSubgroupAsymptotics.PrimitiveSocleFourDivisorOuterFourOrdinary

/-! An actual nonaffine primitive eight-point source whose order is not
divisible by sixteen costs three generators for every paired CFSG model.
Only the actual order360 cases can require an outer order four; their
SAME socle quotient is paid by the original source-order obstruction.
No simple two-generation premise or action catalogue is added. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSoclePairedDegreeEightOrdinary
open PrimitiveSocleRawStructure PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X)

omit [FaithfulSMul G X] in
theorem genRank_le_three_of_outer_le_three (hk : D.factorCount = 1)
    (hhead : MarkedC4.genRank D.Simple ≤ 2)
    (houter : Nat.card (Outer D.Simple) ≤ 3) : MarkedC4.genRank G ≤ 3 := by
  have ho := SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow
    (Nat.card (Outer D.Simple)) 1 (Nat.card_pos (α := Outer D.Simple)) (by norm_num; omega)
  have hg := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  omega

theorem genRank_le_three_of_pair_family (j : CFSG.Index) (hj : PairFamily j)
    (e : D.Simple ≃* j.Model) (hdegree : Nat.card X = 8)
    (hnotSixteen : ¬16 ∣ Nat.card G) : MarkedC4.genRank G ≤ 3 := by
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
  cases j with
  | alternating m hms =>
      by_cases h6 : m = 6
      · subst m
        have hcardT : Nat.card D.Simple = 360 := by
          rw [Nat.card_congr e.toEquiv]
          change Nat.card (alternatingGroup (Fin 6)) = 360
          rw [nat_card_alternatingGroup,Nat.card_fin]
          decide
        have hfour : 4 ∣ Nat.card D.Simple := by rw [hcardT]; decide
        have ho : Nat.card (Outer D.Simple) ≤ 4 := by
          rw [CFSGReduction.outer_card_congr e]
          exact CFSGAlternatingOuterBound.outer_card_le_four 6 hms
        exact PrimitiveSocleFourDivisorOuterFourOrdinary.genRank_le_three
          D hk hhead ho hfour hnotSixteen
      · have ho : Nat.card (Outer D.Simple) ≤ 2 := by
          rw [CFSGReduction.outer_card_congr e]
          change Nat.card (Outer (alternatingGroup (Fin m))) ≤ 2
          rw [CFSGAlternatingOuterBound.outer_card_eq_two_of_ne_six m hms h6]
        exact PrimitiveSocleSmallOuterOrdinaryBudgets.genRank_le_three_of_outer_le_two D hk hhead ho
  | A r q hr hs =>
      letI : IsSimpleGroup (CFSG.Models.A r q) := e.symm.isSimpleGroup
      by_cases h1 : r = 1
      · subst r
        rcases CFSGTypeARankOneDegreeEightOuterAlternative.outer_le_three_or_order_three_sixty
          q ell hellM (by omega) with ho | ⟨hT,ho⟩
        · have hactual : Nat.card (Outer D.Simple) ≤ 3 := by
            simpa only [CFSGReduction.outer_card_congr e] using ho
          exact genRank_le_three_of_outer_le_three D hk hhead hactual
        · have hactual : Nat.card (Outer D.Simple) ≤ 4 := by
            simpa only [CFSGReduction.outer_card_congr e] using ho
          have hcardT : Nat.card D.Simple = 360 := (Nat.card_congr e.toEquiv).trans hT
          have hfour : 4 ∣ Nat.card D.Simple := by rw [hcardT]; decide
          exact PrimitiveSocleFourDivisorOuterFourOrdinary.genRank_le_three
            D hk hhead hactual hfour hnotSixteen
      · have ho := CFSGTypeASmallDegreeOuterBudget.higher_outer_card_le_two r (by omega)
          q ell hellM (by omega)
        have hactual : Nat.card (Outer D.Simple) ≤ 2 := by
          simpa only [CFSGReduction.outer_card_congr e] using ho
        exact PrimitiveSocleSmallOuterOrdinaryBudgets.genRank_le_three_of_outer_le_two D hk hhead hactual
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

theorem genRank_le_three_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (hdegree : Nat.card X = 8) (hnotSixteen : ¬16 ∣ Nat.card G) :
    MarkedC4.genRank G ≤ 3 ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases PrimitiveSocleNonpairDegreeTwentyFour.pair_family_or_actual_remaining_of_degree_below_twenty_four
    D hCFSG (by omega) with ⟨j,hj,⟨e⟩⟩ | hm
  · exact Or.inl (genRank_le_three_of_pair_family D j hj e hdegree hnotSixteen)
  · exact Or.inr hm

end SymmetricSubgroupAsymptotics.PrimitiveSoclePairedDegreeEightOrdinary
