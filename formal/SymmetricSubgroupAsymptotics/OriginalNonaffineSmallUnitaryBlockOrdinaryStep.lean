import SymmetricSubgroupAsymptotics.OriginalNonaffineThirtyTwoOrdinaryStep
import SymmetricSubgroupAsymptotics.CFSGUnitarySmallActualOrdinaryProfiles
import SymmetricSubgroupAsymptotics.NonaffineSmallUnitaryHeadOrdinaryAggregate
import SymmetricSubgroupAsymptotics.NonaffineEightGeneratorSmallDegreeOrdinaryAggregate

/-! Original unitary block induction using the actual bounded profiles.
All local sizes>=32 and five smaller field/rank states are supplied
internally. Only the genuine binary rank-three model is returned as an
explicit residual; no current/global permutation input is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineSmallUnitaryBlockOrdinaryStep
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open OriginalBlockOrdinaryCompressionState ActualWreathChiefUnitMinimumRate
open ActualWreathPrimitiveSocleOuterOrdinaryCost

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

private theorem source_head_cost (i : block.Points) (hk : D.factorCount = 1)
    (H b : ℕ) (hhead : MarkedC4.genRank D.Simple ≤ H)
    (hout : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ b)
    (hbelow : SmallerTransitiveRankBound n) :
    (MarkedC4.genRank J : ℝ) ≤ (H : ℝ)+(b : ℝ)*rate (Nat.card block.Points)+
      traceyPermutationGeneratorCeiling (Nat.card block.Points) := by
  let t := Nat.card block.Points
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
    ((D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
      ArithmeticFunction.cardFactors D.factorCount.factorial : ℕ) : ℝ)*rate t+
        MarkedC4.genRank block.Top at hsource
  simp only [hk,Nat.one_mul,Nat.factorial_one,ArithmeticFunction.cardFactors_one,Nat.add_zero] at hsource
  have hh : (MarkedC4.genRank D.Simple : ℝ) ≤ H := by exact_mod_cast hhead
  have hb : (ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) : ℝ) ≤ b := by exact_mod_cast hout
  have hrate := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ rate t from (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_rate t block.degrees_ge_two.2))
  linarith only [hsource,hh,htop,hrate]

theorem genRank_le_ceiling_or_binary_rank_three (rank : ℕ) (q : CFSG.PrimePower)
    (hrank : 2 ≤ rank) (hs : rank = 2 → q.order ≠ 2)
    (e : D.Simple ≃* CFSG.Models.TwistedA rank q) (i : block.Points)
    (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      (rank = 3 ∧ q.order = 2 ∧ Nat.card block.Fibre < 32) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedA rank q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedA rank q) := Finite.of_equiv D.Simple e.toEquiv
  have hn : ¬ IsMulCommutative (CFSG.Models.TwistedA rank q) := by
    intro h
    exact D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr h)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hm := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  have horder : ell^2 < Nat.card D.Simple := by
    simpa only [Nat.card_congr e.toEquiv] using
      CFSGTwistedAUnitaryCoordinates.twistedA_admissible_leastIndex_square_lt rank hrank q hs ell hm
  have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGTwistedAUnitaryCoordinates.twistedA_admissible_sufficient_outer_budget rank hrank q hs hn ell hm
  by_cases hlarge : 32 ≤ Nat.card block.Fibre
  · exact Or.inl (OriginalNonaffineThirtyTwoOrdinaryStep.genRank_le_ceiling_of_actual_packet
      J block D i hlarge hbelow ell hell horder houter)
  have hsmall : Nat.card block.Fibre < 32 := by omega
  have hfield := CFSGTwistedAUnitaryCoordinates.twistedA_admissible_order_power_le_leastProperIndex
    rank hrank q hs ell hm
  have hellr := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hfieldr := hfield.trans hellr
  rcases CFSGUnitarySmallActualOrdinaryProfiles.profiles rank q hrank hs hn
      (hfieldr.trans_lt hsmall) with hpaid | ⟨hr,hq⟩
  swap
  · exact Or.inr ⟨hr,hq,hsmall⟩
  have hpow8 : 8 ≤ q.order^rank := by
    rcases hpaid with ⟨hh,_,_⟩ | ⟨hh,_,_⟩ | ⟨hh,_,_⟩ | ⟨hh,_,_⟩ <;> omega
  have hell8 : 8 ≤ ell := hpow8.trans hfield
  have hdegree := primitiveSocle_power_le_degree (show 5 ≤ ell by omega) horder (D.degreeForm hell)
  have hk : D.factorCount = 1 := by
    have hp := D.factorCount_pos
    by_contra hh
    have hpow := (Nat.pow_le_pow_right (show 0 < ell by omega)
      (show 2 ≤ D.factorCount by omega)).trans hdegree
    have h64 := Nat.pow_le_pow_left hell8 2
    norm_num at h64
    omega
  let r := Nat.card block.Fibre
  let t := Nat.card block.Points
  have heRank := CoprimeNilpotentProductGenerators.genRank_mulEquiv e
  have hOmega : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) =
      ArithmeticFunction.cardFactors (Nat.card (Outer (CFSG.Models.TwistedA rank q))) := by
    rw [CFSGReduction.outer_card_congr e]
  have hreal : (MarkedC4.genRank J : ℝ) ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
    rcases hpaid with ⟨hr,hhead,hout⟩ | ⟨hr,hhead,hout⟩ | ⟨hr,hhead,hout⟩ | ⟨hr,hhead,hout⟩
    · have hhead' : MarkedC4.genRank D.Simple ≤ 4 := by rw [heRank]; exact hhead
      have hout' : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 1 := by rw [hOmega]; exact hout
      have hc0 := source_head_cost J block D i hk 4 1 hhead' hout' hbelow
      have hc : (MarkedC4.genRank J : ℝ) ≤ 4+1*rate t+traceyPermutationGeneratorCeiling t := by
        simpa only [Nat.cast_ofNat,Nat.cast_one] using hc0
      by_cases h16 : r < 16
      · exact hc.trans (NonaffineSmallUnitaryHeadOrdinaryAggregate.four_generator_cost_le r t
          (hr.trans hfieldr) h16 block.degrees_ge_two.2 4 1
          (by norm_num) (le_refl _) (by norm_num) (le_refl _))
      · exact hc.trans (NonaffineSmallUnitaryHeadOrdinaryAggregate.seven_generator_cost_le r t
          (by omega) hsmall block.degrees_ge_two.2 4 1
          (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    · have hhead' : MarkedC4.genRank D.Simple ≤ 7 := by rw [heRank]; exact hhead
      have hout' : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 2 := by rw [hOmega]; exact hout
      exact (source_head_cost J block D i hk 7 2 hhead' hout' hbelow).trans
        (NonaffineSmallUnitaryHeadOrdinaryAggregate.seven_generator_cost_le r t
          (hr.trans hfieldr) hsmall block.degrees_ge_two.2 7 2
          (by norm_num) (le_refl _) (by norm_num) (le_refl _))
    · have hhead' : MarkedC4.genRank D.Simple ≤ 8 := by rw [heRank]; exact hhead
      have hout' : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 3 := by rw [hOmega]; exact hout
      exact (source_head_cost J block D i hk 8 3 hhead' hout' hbelow).trans
        (NonaffineEightGeneratorSmallDegreeOrdinaryAggregate.eight_generator_cost_le r t
          (hr.trans hfieldr) hsmall block.degrees_ge_two.2 8 3
          (by norm_num) (le_refl _) (by norm_num) (le_refl _))
    · have hhead' : MarkedC4.genRank D.Simple ≤ 11 := by rw [heRank]; exact hhead
      have hout' : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 1 := by rw [hOmega]; exact hout
      have hc0 := source_head_cost J block D i hk 11 1 hhead' hout' hbelow
      have hc : (MarkedC4.genRank J : ℝ) ≤ 11+1*rate t+traceyPermutationGeneratorCeiling t := by
        simpa only [Nat.cast_ofNat,Nat.cast_one] using hc0
      exact hc.trans
        (NonaffineSmallUnitaryHeadOrdinaryAggregate.eleven_generator_cost_le r t
          (hr.trans hfieldr) hsmall block.degrees_ge_two.2 11 1
          (by norm_num) (le_refl _) (by norm_num) (le_refl _))
  have hproduct : r*t = n := by simpa only [Nat.card_fin] using block.degree_product
  have hproductR : (r : ℝ)*(t : ℝ) = (n : ℝ) := by exact_mod_cast hproduct
  simp only [hproductR] at hreal
  have hh := hreal.trans (Nat.le_ceil ((n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ))))
  change (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling n : ℝ) at hh
  exact Or.inl (by exact_mod_cast hh)

theorem exists_generating_finset_or_binary_rank_three (rank : ℕ) (q : CFSG.PrimePower)
    (hrank : 2 ≤ rank) (hs : rank = 2 → q.order ≠ 2)
    (e : D.Simple ≃* CFSG.Models.TwistedA rank q) (i : block.Points)
    (hbelow : SmallerTransitiveRankBound n) :
    (∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧
      F.card ≤ traceyPermutationGeneratorCeiling n) ∨
      (rank = 3 ∧ q.order = 2 ∧ Nat.card block.Fibre < 32) := by
  rcases genRank_le_ceiling_or_binary_rank_three J block D rank q hrank hs e i hbelow with h | h
  · obtain ⟨F,hF,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨F,hgen,hF.le.trans h⟩
  · exact Or.inr h

end SymmetricSubgroupAsymptotics.OriginalNonaffineSmallUnitaryBlockOrdinaryStep
