import SymmetricSubgroupAsymptotics.OriginalNonaffineSmallPairBlockOrdinaryStep
import SymmetricSubgroupAsymptotics.NonaffineTinyPairLargeTopOrdinaryAggregate
import SymmetricSubgroupAsymptotics.NonaffineTinyPairSmallTopOrdinaryCertificates

/-! Completion of the original paired nonaffine block branch at tiny
local degrees. The actual index/outer packet controls the SAME quotient;
no top-action row, stronger induction premise or fictitious simple pair
is supplied. Every original local degree is covered by the final theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineTinyPairBlockOrdinaryStep
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open OriginalBlockOrdinaryCompressionState ActualWreathChiefUnitMinimumRate
open ActualWreathPrimitiveSocleOuterOrdinaryCost

private theorem outer_two {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hr : Nat.card X ≤ 6)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 2 := by
  have hellr := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hell2 : 2 ≤ ell := by
    obtain ⟨H,hH,hindex⟩ := hell.1
    have hh := H.one_lt_index_of_ne_top hH
    omega
  have hpow : ell^3 < 2^8 := (Nat.pow_le_pow_left (show ell ≤ 6 by omega) 3).trans_lt (by decide)
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

private theorem rank_ceiling_of_real (g r t : ℕ)
    (h : (g : ℝ) ≤ (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ)))) :
    g ≤ traceyPermutationGeneratorCeiling (r*t) := by
  have hc : (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) ≤
      (traceyPermutationGeneratorCeiling (r*t) : ℝ) := by
    simpa only [traceyPermutationGeneratorCeiling,Nat.cast_mul] using
      (Nat.le_ceil (((r*t : ℕ) : ℝ)/Real.sqrt (Real.logb 2 ((r*t : ℕ) : ℝ))))
  exact_mod_cast h.trans hc

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)
local instance stateComponentAction : MulAction (initialState J block).D block.Fibre :=
  inferInstanceAs (MulAction block.Component block.Fibre)
local instance stateComponentFaithful : FaithfulSMul (initialState J block).D block.Fibre :=
  inferInstanceAs (FaithfulSMul block.Component block.Fibre)
local instance stateComponentPrimitive : MulAction.IsPreprimitive (initialState J block).D block.Fibre :=
  block.component_preprimitive

variable (D : NonaffineData block.Component block.Fibre)

/-- Both tiny degree bands use the actual ONE-factor socle geometry and
actual outer coefficient, with every inherited top retained. -/
theorem genRank_le_ceiling_of_degree_band (i : block.Points)
    (hr : 5 ≤ Nat.card block.Fibre) (hsmall : Nat.card block.Fibre < 10)
    (S : Finset D.Simple) (hS : Subgroup.closure (S : Set D.Simple) = ⊤) (hcard : S.card ≤ 2)
    (hbelow : SmallerTransitiveRankBound n)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (horder : ell^2 < Nat.card D.Simple)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let r := Nat.card block.Fibre
  let t := Nat.card block.Points
  let B := D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
    ArithmeticFunction.cardFactors D.factorCount.factorial
  obtain ⟨hk,hout3⟩ := PrimitiveSocleDegreeBelowTwentyFiveOuterMultiplicity.factor_and_outer_multiplicity
    D (by omega) ell hell horder houter
  have hB : B = ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) := by
    simp only [B,hk,Nat.one_mul,Nat.factorial_one,ArithmeticFunction.cardFactors_one,Nat.add_zero]
  have hb3 : (B : ℝ) ≤ 3 := by rw [hB]; exact_mod_cast hout3
  have ht : 2 ≤ t := block.degrees_ge_two.2
  have hs : (MarkedC4.genRank D.Simple : ℝ) ≤ 2 := by
    exact_mod_cast (MarkedC4.genRank_le hS).trans hcard
  have htop : (MarkedC4.genRank block.Top : ℝ) ≤ traceyPermutationGeneratorCeiling t := by
    letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
    have hh := rank_of_faithful_transitive_action n hbelow block.Top block.Points
      block.degrees_ge_two.2 (by simpa only [Nat.card_fin] using block.degrees_lt.2)
    exact_mod_cast hh
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have hsource := genRank_le_simple_add_outer_rate_of_one_factor (initialState J block) D i hI hk
  simp only [Fintype.card_eq_nat_card] at hsource
  change (MarkedC4.genRank J : ℝ) ≤ (MarkedC4.genRank D.Simple : ℝ)+
    (B : ℝ)*rate t+MarkedC4.genRank block.Top at hsource
  have hcost : (MarkedC4.genRank J : ℝ) ≤ 2+(B : ℝ)*rate t+traceyPermutationGeneratorCeiling t := by
    linarith only [hsource,hs,htop]
  have hrate : rate t ≤ (t : ℝ)/2 := min_le_left _ _
  have hhalf := mul_le_mul_of_nonneg_left hrate (show (0 : ℝ) ≤ B by positivity)
  have hproduct : r*t = n := by simpa only [Nat.card_fin] using block.degree_product
  have hresult : MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling (r*t) := by
    by_cases hr6 : r ≤ 6
    · have hb2 : (B : ℝ) ≤ 2 := by
        rw [hB]
        exact_mod_cast outer_two D hr6 ell hell houter
      by_cases hlarge : 16 ≤ t
      · exact rank_ceiling_of_real (MarkedC4.genRank J) r t
          (hcost.trans (NonaffineTinyPairLargeTopOrdinaryAggregate.five_six_cost_le
            r t hr hr6 hlarge B hb2))
      · have hh := mul_le_mul_of_nonneg_right hb2 (show 0 ≤ (t : ℝ)/2 by positivity)
        have hcost' : (MarkedC4.genRank J : ℝ) ≤ 2+(t : ℝ)+traceyPermutationGeneratorCeiling t := by
          nlinarith only [hcost,hhalf,hh]
        exact NonaffineTinyPairSmallTopOrdinaryCertificates.five_six_rank_le
          r t (MarkedC4.genRank J) hr hr6 ht (by omega) hcost'
    · have hr7 : 7 ≤ r := by omega
      have hr9 : r ≤ 9 := by omega
      by_cases hlarge : 16 ≤ t
      · exact rank_ceiling_of_real (MarkedC4.genRank J) r t
          (hcost.trans (NonaffineTinyPairLargeTopOrdinaryAggregate.seven_nine_cost_le
            r t hr7 hr9 hlarge B hb3))
      · have hh := mul_le_mul_of_nonneg_right hb3 (show 0 ≤ (t : ℝ)/2 by positivity)
        have hcost' : (MarkedC4.genRank J : ℝ) ≤ 2+3*(t : ℝ)/2+traceyPermutationGeneratorCeiling t := by
          nlinarith only [hcost,hhalf,hh]
        exact NonaffineTinyPairSmallTopOrdinaryCertificates.seven_nine_rank_le
          r t (MarkedC4.genRank J) hr7 hr9 ht (by omega) hcost'
  simpa only [hproduct] using hresult

/-- The actual pair and actual index packet now pay EVERY nonaffine local
degree, not only a bounded or asymptotic fibre range. -/
theorem genRank_le_ceiling (i : block.Points)
    (S : Finset D.Simple) (hS : Subgroup.closure (S : Set D.Simple) = ⊤) (hcard : S.card ≤ 2)
    (hbelow : SmallerTransitiveRankBound n)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (horder : ell^2 < Nat.card D.Simple)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  by_cases hlarge : 10 ≤ Nat.card block.Fibre
  · exact OriginalNonaffineSmallPairBlockOrdinaryStep.genRank_le_ceiling
      J block D i hlarge S hS hcard hbelow ell hell horder houter
  · have hell5 : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
      (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
    have hr := hell5.trans (PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell)
    exact genRank_le_ceiling_of_degree_band J block D i hr (by omega)
      S hS hcard hbelow ell hell horder houter

theorem genRank_le_ceiling_of_model {M : Type} [Group M] (e : D.Simple ≃* M)
    (hpair : ∃ S : Finset M, Subgroup.closure (S : Set M) = ⊤ ∧ S.card ≤ 2)
    (hpacket : ∀ ell : ℕ, LeastProperIndex M ell →
      ell^2 < Nat.card M ∧ SufficientOuterOrderBudget ell (Nat.card (Outer M)))
    (i : block.Points) (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
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
  exact genRank_le_ceiling J block D i U hU hUcard hbelow ell hell horder houter

theorem exists_generating_finset (i : block.Points)
    (S : Finset D.Simple) (hS : Subgroup.closure (S : Set D.Simple) = ⊤) (hcard : S.card ≤ 2)
    (hbelow : SmallerTransitiveRankBound n)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (horder : ell^2 < Nat.card D.Simple)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    ∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧
      F.card ≤ traceyPermutationGeneratorCeiling n := by
  obtain ⟨F,hF,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨F,hgen,hF.le.trans (genRank_le_ceiling J block D i S hS hcard hbelow ell hell horder houter)⟩

end SymmetricSubgroupAsymptotics.OriginalNonaffineTinyPairBlockOrdinaryStep
