import SymmetricSubgroupAsymptotics.OriginalNonaffineTinyPairBlockOrdinaryStep
import SymmetricSubgroupAsymptotics.NonaffineTripleSmallDegreeOrdinaryAggregate

/-! The same three-generator simple head pays every inherited top in
local degrees 20 through 31. Its actual outer quotient, rather than a
separate quotient bound, enters the original block recurrence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineTripleSmallDegreeOrdinaryStep
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open OriginalBlockOrdinaryCompressionState ActualWreathChiefUnitMinimumRate
open ActualWreathPrimitiveSocleOuterOrdinaryCost

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by have h := block.degrees_ge_two.1; omega)
local instance stateComponentAction : MulAction (initialState J block).D block.Fibre :=
  inferInstanceAs (MulAction block.Component block.Fibre)
local instance stateComponentFaithful : FaithfulSMul (initialState J block).D block.Fibre :=
  inferInstanceAs (FaithfulSMul block.Component block.Fibre)
local instance stateComponentPrimitive : MulAction.IsPreprimitive (initialState J block).D block.Fibre :=
  block.component_preprimitive

variable (D : NonaffineData block.Component block.Fibre)

theorem genRank_le_ceiling (i : block.Points)
    (hr : 20 ≤ Nat.card block.Fibre) (hsmall : Nat.card block.Fibre ≤ 31)
    (hk : D.factorCount = 1) (hs : MarkedC4.genRank D.Simple ≤ 3)
    (hbelow : SmallerTransitiveRankBound n)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let r := Nat.card block.Fibre
  let t := Nat.card block.Points
  let B := D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
    ArithmeticFunction.cardFactors D.factorCount.factorial
  have hB : B = ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) := by
    simp only [B,hk,Nat.one_mul,Nat.factorial_one,ArithmeticFunction.cardFactors_one,Nat.add_zero]
  have hell0 : 0 < ell := by
    obtain ⟨H,hH,_⟩ := hell.1
    have h := H.one_lt_index_of_ne_top hH
    omega
  have hdegree := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hlog : Real.logb 2 (r : ℝ) ≤ 5 := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper r 1 5 (by omega) (by decide)
      (by simpa only [pow_one] using (show r ≤ 2^5 by omega))
    simpa only [Nat.cast_one,div_one] using hh
  have hout : (Nat.card (Outer D.Simple) : ℝ) ≤ 32 := by
    have h := houter.log_six_of_le hell0 hdegree
    linarith only [h,hlog]
  have h32 : Real.logb 2 (32 : ℝ) = 5 := by
    rw [show (32 : ℝ) = 2^5 by norm_num,Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  have hlogOut : Real.logb 2 (Nat.card (Outer D.Simple) : ℝ) ≤ 5 := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (Nat.card_pos (α := Outer D.Simple))) hout
    simpa only [h32] using h
  have hb : (B : ℝ) ≤ 5 := by
    rw [hB]
    exact (ActualWreathUniformLocalOrderCost.cardFactors_le_logb
      (Nat.card (Outer D.Simple)) (Nat.card_pos (α := Outer D.Simple)).ne').trans hlogOut
  have ht : 2 ≤ t := block.degrees_ge_two.2
  have htop : (MarkedC4.genRank block.Top : ℝ) ≤ traceyPermutationGeneratorCeiling t := by
    letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
    exact_mod_cast rank_of_faithful_transitive_action n hbelow block.Top block.Points
      block.degrees_ge_two.2 (by simpa only [Nat.card_fin] using block.degrees_lt.2)
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using ht
  have hsource := genRank_le_simple_add_outer_rate_of_one_factor (initialState J block) D i hI hk
  simp only [Fintype.card_eq_nat_card] at hsource
  change (MarkedC4.genRank J : ℝ) ≤ (MarkedC4.genRank D.Simple : ℝ)+
    (B : ℝ)*rate t+MarkedC4.genRank block.Top at hsource
  have hsR : (MarkedC4.genRank D.Simple : ℝ) ≤ 3 := by exact_mod_cast hs
  have hcost : (MarkedC4.genRank J : ℝ) ≤ 3+(B : ℝ)*rate t+traceyPermutationGeneratorCeiling t := by
    linarith only [hsource,hsR,htop]
  have hnum := NonaffineTripleSmallDegreeOrdinaryAggregate.cost_le r t hr hsmall ht B hb
  have hproduct : r*t = n := by simpa only [Nat.card_fin] using block.degree_product
  have hceil : (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) ≤
      (traceyPermutationGeneratorCeiling n : ℝ) := by
    simpa only [←hproduct,traceyPermutationGeneratorCeiling,Nat.cast_mul] using
      Nat.le_ceil (((r*t : ℕ) : ℝ)/Real.sqrt (Real.logb 2 ((r*t : ℕ) : ℝ)))
  exact_mod_cast (hcost.trans hnum).trans hceil

end SymmetricSubgroupAsymptotics.OriginalNonaffineTripleSmallDegreeOrdinaryStep
