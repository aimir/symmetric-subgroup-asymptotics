import SymmetricSubgroupAsymptotics.ActualWreathPrimeTopSocleOrdinaryCost
import SymmetricSubgroupAsymptotics.TinyPrimeTopSharpFloorNumerics
import SymmetricSubgroupAsymptotics.OriginalNonaffinePairFamiliesAllDegreeOrdinaryStep

/-! The three tiny nonaffine prime-top seams use one actual socle quotient
and one actual chief trace. The explicit pair-family corollary supplies its
proved pair and index packet internally. The target is the literal published
sharp FLOOR, not only half degree. No current/smaller Tracey or MN hypothesis
occurs, and no permutation action catalogue is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffinePrimeTopTinySharpStep
open PrimitiveSocleRawStructure OriginalBlockOrdinaryCompressionState
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open TraceySharpHalfDegreeNumerics

theorem outer_cardFactors_le_two_of_degree_le_six
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hr : Nat.card X ≤ 6)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 2 := by
  have hellr := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hell2 : 2 ≤ ell := by
    obtain ⟨H,hH,hindex⟩ := hell.1
    have hh := H.one_lt_index_of_ne_top hH
    omega
  have hpow : ell^3 < 2^8 :=
    (Nat.pow_le_pow_left (show ell ≤ 6 by omega) 3).trans_lt (by decide)
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by exact_mod_cast (show 0 < ell by omega) : (0 : ℝ) < ell) 3)
    (show (ell : ℝ)^3 < (2 : ℝ)^8 by exact_mod_cast hpow)
  simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at hlog
  have hout := houter.log_three_of_small (by omega)
  have hN : Nat.card (Outer D.Simple) < 2^(2+1) := by
    have hh : (Nat.card (Outer D.Simple) : ℝ) < 8 := hout.trans_lt hlog
    exact_mod_cast hh
  exact SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow
    (Nat.card (Outer D.Simple)) 2 Nat.card_pos hN

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

private theorem top_rank (ht : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3) :
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

/-- Only literal original local/top degrees are matched. Neither full S3
top nor any other top is removed: top degree three costs its actual rank≤2. -/
theorem genRank_le_sharpFloor
    (hshape : (Nat.card block.Fibre = 6 ∧ Nat.card block.Points = 2) ∨
      (Nat.card block.Fibre = 5 ∧ Nat.card block.Points = 3) ∨
      (Nat.card block.Fibre = 7 ∧ Nat.card block.Points = 3))
    (S : Finset D.Simple) (hS : Subgroup.closure (S : Set D.Simple) = ⊤) (hcard : S.card ≤ 2)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (horder : ell^2 < Nat.card D.Simple)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    MarkedC4.genRank J ≤ sharpFloor n := by
  have hr : Nat.card block.Fibre < 25 := by rcases hshape with h|h|h <;> omega
  have ht : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 := by
    rcases hshape with h|h|h <;> omega
  have hprime : (Fintype.card block.Points).Prime := by
    rw [Fintype.card_eq_nat_card]
    rcases ht with ht|ht <;> rw [ht] <;> decide
  obtain ⟨hk,hout3⟩ :=
    PrimitiveSocleDegreeBelowTwentyFiveOuterMultiplicity.factor_and_outer_multiplicity
      D hr ell hell horder houter
  have hs : MarkedC4.genRank D.Simple ≤ 2 := (MarkedC4.genRank_le hS).trans hcard
  have htop := top_rank J block ht
  have hsource := ActualWreathPrimeTopSocleOrdinaryCost.genRank_le_simple_add_outer_add_top_of_one_factor
    (initialState J block) D block.base hprime hk
  change MarkedC4.genRank J ≤ MarkedC4.genRank D.Simple +
    ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) + MarkedC4.genRank block.Top at hsource
  have hproduct : Nat.card block.Fibre * Nat.card block.Points = n := by
    simpa only [Nat.card_fin] using block.degree_product
  rcases hshape with ⟨hr,ht⟩ | ⟨hr,ht⟩ | ⟨hr,ht⟩
  · have hout2 := outer_cardFactors_le_two_of_degree_le_six D (by omega) ell hell houter
    have hg : MarkedC4.genRank J ≤ 5 := by omega
    have hn : n = 12 := by rw [hr,ht] at hproduct; omega
    have hf : 5 ≤ sharpFloor n := by
      simpa only [hn] using TinyPrimeTopSharpFloorNumerics.five_le_sharpFloor_twelve
    exact hg.trans hf
  · have hout2 := outer_cardFactors_le_two_of_degree_le_six D (by omega) ell hell houter
    have hg : MarkedC4.genRank J ≤ 6 := by omega
    have hn : n = 15 := by rw [hr,ht] at hproduct; omega
    have hf : 6 ≤ sharpFloor n := by
      simpa only [hn] using TinyPrimeTopSharpFloorNumerics.six_le_sharpFloor_fifteen
    exact hg.trans hf
  · have hg : MarkedC4.genRank J ≤ 8 := by omega
    have hn : n = 21 := by rw [hr,ht] at hproduct; omega
    have hf : 8 ≤ sharpFloor n := by
      simpa only [hn] using TinyPrimeTopSharpFloorNumerics.eight_le_sharpFloor_twenty_one
    exact hg.trans hf

theorem genRank_le_sharpFloor_of_model {M : Type} [Group M]
    (e : D.Simple ≃* M)
    (hpair : ∃ S : Finset M, Subgroup.closure (S : Set M) = ⊤ ∧ S.card ≤ 2)
    (hpacket : ∀ ell : ℕ, LeastProperIndex M ell →
      ell^2 < Nat.card M ∧ SufficientOuterOrderBudget ell (Nat.card (Outer M)))
    (hshape : (Nat.card block.Fibre = 6 ∧ Nat.card block.Points = 2) ∨
      (Nat.card block.Fibre = 5 ∧ Nat.card block.Points = 3) ∨
      (Nat.card block.Fibre = 7 ∧ Nat.card block.Points = 3)) :
    MarkedC4.genRank J ≤ sharpFloor n := by
  classical
  obtain ⟨S,hS,hcard⟩ := hpair
  let U := S.image e.symm
  have hU : Subgroup.closure (U : Set D.Simple) = ⊤ := by
    rw [Finset.coe_image]
    change Subgroup.closure (e.symm.toMonoidHom '' (S : Set M)) = ⊤
    rw [← MonoidHom.map_closure,hS]
    exact Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hUcard : U.card ≤ 2 := Finset.card_image_le.trans hcard
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hm := hpacket ell (CFSGReduction.leastProperIndex_of_mulEquiv e ell hell)
  have horder : ell^2 < Nat.card D.Simple := by
    simpa only [Nat.card_congr e.toEquiv] using hm.1
  have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
    rw [CFSGReduction.outer_card_congr e]
    exact hm.2
  exact genRank_le_sharpFloor J block D hshape U hU hUcard ell hell horder houter

/-- The proved literal family constructors supply both the pair and its
same-model index/outer packet; no extra family callback remains. -/
theorem genRank_le_sharpFloor_of_pair_family (j : CFSG.Index) (hj : PairFamily j)
    (e : D.Simple ≃* j.Model)
    (hshape : (Nat.card block.Fibre = 6 ∧ Nat.card block.Points = 2) ∨
      (Nat.card block.Fibre = 5 ∧ Nat.card block.Points = 3) ∨
      (Nat.card block.Fibre = 7 ∧ Nat.card block.Points = 3)) :
    MarkedC4.genRank J ≤ sharpFloor n := by
  letI : Finite j.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup j.Model := e.symm.isSimpleGroup
  have hn : ¬ IsMulCommutative j.Model := by
    intro hh
    exact D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr hh)
  rcases CFSGSimpleIndexPacketOrTitsSporadic.model_packet_or_remaining j hn with hp | hr
  · exact genRank_le_sharpFloor_of_model J block D e
      (OriginalNonaffineSmallPairFamiliesBlockOrdinaryStep.model_pair_of_family j hj) hp hshape
  · have hnot : ¬ RemainingModel j := by
      cases j <;> simp_all only [PairFamily,RemainingModel,not_false_eq_true]
    exact (hnot hr).elim

theorem exists_generating_finset_of_pair_family (j : CFSG.Index) (hj : PairFamily j)
    (e : D.Simple ≃* j.Model)
    (hshape : (Nat.card block.Fibre = 6 ∧ Nat.card block.Points = 2) ∨
      (Nat.card block.Fibre = 5 ∧ Nat.card block.Points = 3) ∨
      (Nat.card block.Fibre = 7 ∧ Nat.card block.Points = 3)) :
    ∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧ F.card ≤ sharpFloor n := by
  obtain ⟨F,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨F,hgen,hcard.le.trans (genRank_le_sharpFloor_of_pair_family J block D j hj e hshape)⟩

end SymmetricSubgroupAsymptotics.OriginalNonaffinePrimeTopTinySharpStep
