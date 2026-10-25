import SymmetricSubgroupAsymptotics.OriginalNonaffineFiveByTwoSharpCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleNonpairDegreeTwentyFour
import SymmetricSubgroupAsymptotics.SmallFourPointOrdinaryGenerators

/-! ALL original nonaffine imprimitive actions below degree22 meet the
literal published sharp FLOOR, except for actual Tits/sporadic factor
witnesses. The same chief trace pays prime tops; the actual half-capacity
pays top4. Index5 recognition supplies the exceptional local5/top2 saving.
Only integer block-degree geometry is split, never a permutation-group
catalogue. No smaller/global Tracey or MN hypothesis is assumed. Affine
primitive and affine-block sharp questions are separate from this result. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineBoundedSharpCFSGReduction
open PrimitiveSocleRawStructure OriginalBlockOrdinaryCompressionState
open ActualWreathPrimitiveSocleOuterOrdinaryCost ActualWreathChiefUnitMinimumRate
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction TraceySharpHalfDegreeNumerics
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)

theorem six_le_sharpFloor_of_band (n : ℕ) (hlo : 14 ≤ n) (hhi : n ≤ 21) :
    6 ≤ sharpFloor n := by
  by_cases hb : n ≤ 16
  · exact TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square n 6 4 (by omega)
      (TinyPrimeTopSharpFloorNumerics.log_le_of_pow n 4 (by omega) (by simpa using hb))
      (by have hh := Nat.pow_le_pow_left hlo 2; norm_num at hh ⊢; omega)
  · exact TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square n 6 5 (by omega)
      (TinyPrimeTopSharpFloorNumerics.log_le_of_pow n 5 (by omega) (by norm_num; omega))
      (by have hh := Nat.pow_le_pow_left (show 17 ≤ n by omega) 2; norm_num at hh ⊢; omega)

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

private theorem prime_top_rank (ht : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3) :
    MarkedC4.genRank block.Top ≤ Nat.card block.Points - 1 := by
  have hcard : Nat.card block.Top ≤ (Nat.card block.Points).factorial := by
    simpa only [Nat.card_perm] using Nat.card_le_card_of_injective
      (MulAction.toPermHom block.Top block.Points) MulAction.toPerm_injective
  rcases ht with ht | ht
  · rw [ht] at hcard ⊢
    exact FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow block.Top 1
      (by simpa using hcard)
  · rw [ht] at hcard ⊢
    norm_num only [Nat.factorial_succ,Nat.factorial_zero] at hcard
    by_contra hh
    have hg : 3 ≤ MarkedC4.genRank block.Top := by omega
    have hp := (Nat.pow_le_pow_right (by decide : 0 < 2) hg).trans
      ((FiniteGroupBinaryOrderGenerators.two_pow_genRank_le_card block.Top).trans hcard)
    norm_num at hp

variable (D : NonaffineData block.Component block.Fibre)

local instance stateComponentAction : MulAction (initialState J block).D block.Fibre :=
  inferInstanceAs (MulAction block.Component block.Fibre)

theorem genRank_le_sharpFloor_of_actual_pair_packet (hsmall : n < 22)
    (S : Finset D.Simple) (hS : Subgroup.closure (S : Set D.Simple) = ⊤) (hcard : S.card ≤ 2)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (horder : ell^2 < Nat.card D.Simple)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    MarkedC4.genRank J ≤ sharpFloor n := by
  have hproduct : Nat.card block.Fibre * Nat.card block.Points = n := by
    simpa only [Nat.card_fin] using block.degree_product
  have ht2 := block.degrees_ge_two.2
  have hell5 : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun hh => D.noncommutative (isMulCommutative_iff.mpr hh)) hell.1
  have hellr := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hr5 : 5 ≤ Nat.card block.Fibre := hell5.trans hellr
  have ht4 : Nat.card block.Points ≤ 4 := by
    have hh := (Nat.mul_le_mul_right (Nat.card block.Points) hr5).trans_eq hproduct
    omega
  have hr10 : Nat.card block.Fibre ≤ 10 := by
    have hh := (Nat.mul_le_mul_left (Nat.card block.Fibre) ht2).trans_eq hproduct
    omega
  obtain ⟨hk,hout3⟩ :=
    PrimitiveSocleDegreeBelowTwentyFiveOuterMultiplicity.factor_and_outer_multiplicity
      D (by omega) ell hell horder houter
  have hs : MarkedC4.genRank D.Simple ≤ 2 := (MarkedC4.genRank_le hS).trans hcard
  have htCases : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 ∨
      Nat.card block.Points = 4 := by omega
  rcases htCases with ht | ht | ht
  · by_cases hr : Nat.card block.Fibre = 5
    · have hg := OriginalNonaffineFiveByTwoSharpCFSGReduction.genRank_le_four_of_actual_index_square
        J block D hr ht ell hell horder
      have hn : n = 10 := by rw [hr,ht] at hproduct; omega
      have hf : 4 ≤ sharpFloor n := by
        simpa only [hn] using SmallPrimeTopSharpFloorCertificates.four_le_sharpFloor_ten
      exact hg.trans hf
    have hprime : (Fintype.card block.Points).Prime := by rw [Fintype.card_eq_nat_card,ht]; decide
    have htop := prime_top_rank J block (Or.inl ht)
    have hsource := ActualWreathPrimeTopSocleOrdinaryCost.genRank_le_simple_add_outer_add_top_of_one_factor
      (initialState J block) D block.base hprime hk
    change MarkedC4.genRank J ≤ MarkedC4.genRank D.Simple +
      ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) + MarkedC4.genRank block.Top at hsource
    by_cases hr6 : Nat.card block.Fibre = 6
    · have hout2 := OriginalNonaffinePrimeTopTinySharpStep.outer_cardFactors_le_two_of_degree_le_six
        D (by omega) ell hell houter
      have hg : MarkedC4.genRank J ≤ 5 := by omega
      have hn : n = 12 := by rw [hr6,ht] at hproduct; omega
      have hf : 5 ≤ sharpFloor n := by
        simpa only [hn] using TinyPrimeTopSharpFloorNumerics.five_le_sharpFloor_twelve
      exact hg.trans hf
    · have hg : MarkedC4.genRank J ≤ 6 := by omega
      have hn : 14 ≤ n := by rw [ht] at hproduct; omega
      exact hg.trans (six_le_sharpFloor_of_band n hn (by omega))
  · have hprime : (Fintype.card block.Points).Prime := by rw [Fintype.card_eq_nat_card,ht]; decide
    have htop := prime_top_rank J block (Or.inr ht)
    have hsource := ActualWreathPrimeTopSocleOrdinaryCost.genRank_le_simple_add_outer_add_top_of_one_factor
      (initialState J block) D block.base hprime hk
    change MarkedC4.genRank J ≤ MarkedC4.genRank D.Simple +
      ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) + MarkedC4.genRank block.Top at hsource
    by_cases hr6 : Nat.card block.Fibre ≤ 6
    · have hout2 := OriginalNonaffinePrimeTopTinySharpStep.outer_cardFactors_le_two_of_degree_le_six
        D hr6 ell hell houter
      have hg : MarkedC4.genRank J ≤ 6 := by omega
      have hn : 14 ≤ n := by rw [ht] at hproduct; omega
      exact hg.trans (six_le_sharpFloor_of_band n hn (by omega))
    · have hr7 : Nat.card block.Fibre = 7 := by rw [ht] at hproduct; omega
      have hg : MarkedC4.genRank J ≤ 8 := by omega
      have hn : n = 21 := by rw [hr7,ht] at hproduct; omega
      have hf : 8 ≤ sharpFloor n := by
        simpa only [hn] using TinyPrimeTopSharpFloorNumerics.eight_le_sharpFloor_twenty_one
      exact hg.trans hf
  · have hr : Nat.card block.Fibre = 5 := by rw [ht] at hproduct; omega
    have hout2 := OriginalNonaffinePrimeTopTinySharpStep.outer_cardFactors_le_two_of_degree_le_six
      D (by omega) ell hell houter
    have htop := SmallFourPointOrdinaryGenerators.genRank_le_two
      (G := block.Top) (X := block.Points) ht
    have hI : 2 ≤ Fintype.card block.Points := by rw [Fintype.card_eq_nat_card,ht]; decide
    have hsource := genRank_le_simple_add_outer_rate_of_one_factor (initialState J block) D block.base hI hk
    have ho : outerMultiplicity (initialState J block) D =
        ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) := by
      simp only [outerMultiplicity,hk,one_mul,Nat.factorial_one,
        ArithmeticFunction.cardFactors_one,add_zero]
    rw [ho] at hsource
    simp only [Fintype.card_eq_nat_card,ht] at hsource
    change (MarkedC4.genRank J : ℝ) ≤ (MarkedC4.genRank D.Simple : ℝ) +
      (ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) : ℝ)*rate 4 +
        MarkedC4.genRank block.Top at hsource
    have hrate : rate 4 ≤ 2 := by
      have hh : rate 4 ≤ (4 : ℝ)/2 := min_le_left _ _
      norm_num at hh
      exact hh
    have hmul := mul_le_mul_of_nonneg_left hrate
      (show (0 : ℝ) ≤ ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) by positivity)
    have hsR : (MarkedC4.genRank D.Simple : ℝ) ≤ 2 := by exact_mod_cast hs
    have hoR : (ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) : ℝ) ≤ 2 := by
      exact_mod_cast hout2
    have htR : (MarkedC4.genRank block.Top : ℝ) ≤ 2 := by exact_mod_cast htop
    have hgR : (MarkedC4.genRank J : ℝ) ≤ 8 := by nlinarith only [hsource,hmul,hsR,hoR,htR]
    have hg : MarkedC4.genRank J ≤ 8 := by exact_mod_cast hgR
    have hn : n = 20 := by rw [hr,ht] at hproduct; omega
    have hf : 8 ≤ sharpFloor n := by
      simpa only [hn] using SmallPrimeTopSharpFloorCertificates.eight_le_sharpFloor_twenty
    exact hg.trans hf

theorem genRank_le_sharpFloor_of_pair_family (j : CFSG.Index) (hj : PairFamily j)
    (e : D.Simple ≃* j.Model) (hsmall : n < 22) : MarkedC4.genRank J ≤ sharpFloor n := by
  classical
  letI : Finite j.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup j.Model := e.symm.isSimpleGroup
  have hn : ¬ IsMulCommutative j.Model := by
    intro hh
    exact D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr hh)
  rcases CFSGSimpleIndexPacketOrTitsSporadic.model_packet_or_remaining j hn with hp | hr
  · obtain ⟨S,hS,hcard⟩ := OriginalNonaffineSmallPairFamiliesBlockOrdinaryStep.model_pair_of_family j hj
    let U := S.image e.symm
    have hU : Subgroup.closure (U : Set D.Simple) = ⊤ := by
      rw [Finset.coe_image]
      change Subgroup.closure (e.symm.toMonoidHom '' (S : Set j.Model)) = ⊤
      rw [← MonoidHom.map_closure,hS]
      exact Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective
    have hUcard : U.card ≤ 2 := Finset.card_image_le.trans hcard
    obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
    have hm := hp ell (CFSGReduction.leastProperIndex_of_mulEquiv e ell hell)
    have horder : ell^2 < Nat.card D.Simple := by simpa only [Nat.card_congr e.toEquiv] using hm.1
    have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
      rw [CFSGReduction.outer_card_congr e]
      exact hm.2
    exact genRank_le_sharpFloor_of_actual_pair_packet J block D hsmall U hU hUcard ell hell horder houter
  · have hnot : ¬ RemainingModel j := by
      cases j <;> simp_all only [PairFamily,RemainingModel,not_false_eq_true]
    exact (hnot hr).elim

theorem genRank_le_sharpFloor_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (hsmall : n < 22) : MarkedC4.genRank J ≤ sharpFloor n ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  have ht := block.degrees_ge_two.2
  have hproduct : Nat.card block.Fibre * Nat.card block.Points = n := by
    simpa only [Nat.card_fin] using block.degree_product
  have hr : Nat.card block.Fibre < 24 := by
    have hh := (Nat.mul_le_mul_left (Nat.card block.Fibre) ht).trans_eq hproduct
    omega
  rcases PrimitiveSocleNonpairDegreeTwentyFour.pair_family_or_actual_remaining_of_degree_below_twenty_four
    D hCFSG hr with ⟨j,hj,⟨e⟩⟩ | hm
  · exact Or.inl (genRank_le_sharpFloor_of_pair_family J block D j hj e hsmall)
  · exact Or.inr hm

theorem exists_generating_finset_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (hsmall : n < 22) :
    (∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧ F.card ≤ sharpFloor n) ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases genRank_le_sharpFloor_or_actual_remaining_model J block D hCFSG hsmall with hg | hm
  · obtain ⟨F,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨F,hgen,hcard.le.trans hg⟩
  · exact Or.inr hm

end SymmetricSubgroupAsymptotics.OriginalNonaffineBoundedSharpCFSGReduction
