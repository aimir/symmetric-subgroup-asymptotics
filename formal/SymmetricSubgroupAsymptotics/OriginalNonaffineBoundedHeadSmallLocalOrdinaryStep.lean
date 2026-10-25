import SymmetricSubgroupAsymptotics.NonaffineBoundedHeadSmallLocalOrdinaryAggregate
import SymmetricSubgroupAsymptotics.OriginalNonaffinePairFamiliesAllDegreeOrdinaryStep
import SymmetricSubgroupAsymptotics.SimpleLeastIndexFiveRecognition
import SymmetricSubgroupAsymptotics.PrimitiveSocleDegreeBelowTwentyFiveOuterMultiplicity

/-! One actual original-block installer for bounded genuine ordinary heads.
The explicit packet belongs to the SAME simple factor and least index.
Multiple factors below local degree32 force least index5; actual A5
recognition then supplies the existing unconditional pair-family consumer.
The remaining one-factor branch uses the literal compressed source,
outer-chief quotient and strictly-smaller TRANSITIVE top induction.
No model callback or fitted aggregate is introduced. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineBoundedHeadSmallLocalOrdinaryStep
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open OriginalBlockOrdinaryCompressionState ActualWreathChiefUnitMinimumRate
open ActualWreathPrimitiveSocleOuterOrdinaryCost

private theorem outer_cardFactors_le_four (ell N : ℕ) (hN : 0 < N)
    (houter : SufficientOuterOrderBudget ell N) (hell : 0 < ell)
    (h32 : ell < 32) : ArithmeticFunction.cardFactors N ≤ 4 := by
  have hh := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hell : (0 : ℝ) < ell)
    (by exact_mod_cast h32 : (ell : ℝ) < 32)
  have hlog : Real.logb 2 (32 : ℝ) = 5 := by
    rw [show (32 : ℝ) = 2^5 by norm_num,Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  rw [hlog] at hh
  apply SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow N 4 hN
  have hNR : (N : ℝ) < 32 := by linarith only [houter.log_six,hh]
  exact_mod_cast hNR

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

/-- The two genuine head bands, with no assumed one-factor restriction.
All index/order/outer data are explicit and refer to the SAME factor. -/
theorem genRank_le_ceiling (i : block.Points) (hsmall : Nat.card block.Fibre < 32)
    (hhead : (20 ≤ Nat.card block.Fibre ∧ MarkedC4.genRank D.Simple ≤ 10) ∨
      (18 ≤ Nat.card block.Fibre ∧ MarkedC4.genRank D.Simple ≤ 7))
    (hbelow : SmallerTransitiveRankBound n)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (horder : ell^2 < Nat.card D.Simple)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  have hell5 : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  have hdegree := primitiveSocle_power_le_degree hell5 horder (D.degreeForm hell)
  by_cases hk : D.factorCount = 1
  · let r := Nat.card block.Fibre
    let t := Nat.card block.Points
    let B := ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))
    have ht : 2 ≤ t := block.degrees_ge_two.2
    have hellr : ell ≤ r := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
    have hb4 : B ≤ 4 := outer_cardFactors_le_four ell _ Nat.card_pos houter (by omega) (by omega)
    have htop : (MarkedC4.genRank block.Top : ℝ) ≤ traceyPermutationGeneratorCeiling t := by
      letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
      exact_mod_cast rank_of_faithful_transitive_action n hbelow block.Top block.Points
        block.degrees_ge_two.2 (by simpa only [Nat.card_fin] using block.degrees_lt.2)
    have hI : 2 ≤ Fintype.card block.Points := by
      simpa only [Fintype.card_eq_nat_card] using ht
    have hsource := genRank_le_simple_add_outer_rate_of_one_factor (initialState J block) D i hI hk
    simp only [outerMultiplicity,hk,Nat.one_mul,Nat.factorial_one,
      ArithmeticFunction.cardFactors_one,Nat.add_zero,Fintype.card_eq_nat_card] at hsource
    change (MarkedC4.genRank J : ℝ) ≤ (MarkedC4.genRank D.Simple : ℝ)+
      (B : ℝ)*rate t+MarkedC4.genRank block.Top at hsource
    have hcost : (MarkedC4.genRank J : ℝ) ≤ (MarkedC4.genRank D.Simple : ℝ)+
      (B : ℝ)*rate t+traceyPermutationGeneratorCeiling t := by
      linarith only [hsource,htop]
    have hnum : (MarkedC4.genRank D.Simple : ℝ)+(B : ℝ)*rate t+
        traceyPermutationGeneratorCeiling t ≤
        (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
      rcases hhead with ⟨hr,hH⟩ | ⟨hr,hH⟩
      · have hb : (B : ℝ) ≤ if r < 22 then 3 else 4 := by
          by_cases hl : r < 22
          · have hb3 := (PrimitiveSocleDegreeBelowTwentyFiveOuterMultiplicity.factor_and_outer_multiplicity
              D (by omega) ell hell horder houter).2
            have hb3R : (B : ℝ) ≤ 3 := by exact_mod_cast hb3
            simpa only [if_pos hl] using hb3R
          · have hb4R : (B : ℝ) ≤ 4 := by exact_mod_cast hb4
            simpa only [if_neg hl] using hb4R
        exact NonaffineBoundedHeadSmallLocalOrdinaryAggregate.ten_generator_cost_le
          r t hr hsmall ht _ _ (by positivity) (by exact_mod_cast hH) (by positivity) hb
      · exact NonaffineBoundedHeadSmallLocalOrdinaryAggregate.seven_generator_cost_le
          r t hr hsmall ht _ _ (by positivity) (by exact_mod_cast hH) (by positivity)
          (by exact_mod_cast hb4)
    have hreal := hcost.trans hnum
    have hproduct : r*t = n := by simpa only [Nat.card_fin] using block.degree_product
    have hproductR : (r : ℝ)*(t : ℝ) = (n : ℝ) := by exact_mod_cast hproduct
    rw [hproductR] at hreal
    have hh := hreal.trans (Nat.le_ceil ((n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ))))
    change (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling n : ℝ) at hh
    exact_mod_cast hh
  · have hk2 : 2 ≤ D.factorCount := by have hp := D.factorCount_pos; omega
    have he5 : ell = 5 := by
      by_contra he
      have h6 : 6 ≤ ell := by omega
      have hp := (Nat.pow_le_pow_right (by decide : 0 < 6) hk2).trans
        ((Nat.pow_le_pow_left h6 D.factorCount).trans hdegree)
      change 36 ≤ Nat.card block.Fibre at hp
      omega
    have hellFive : LeastProperIndex D.Simple 5 := by simpa only [he5] using hell
    have horderFive : 5^2 < Nat.card D.Simple := by simpa only [he5] using horder
    obtain ⟨eA⟩ := SimpleLeastIndexFiveRecognition.exists_mulEquiv_alternating_five
      D.Simple D.noncommutative hellFive horderFive
    have eModel : D.Simple ≃* (CFSG.Index.alternating 5 (by decide)).Model := by
      simpa only [CFSG.Index.instGroupModel,CFSG.Index.Model] using eA
    exact OriginalNonaffinePairFamiliesAllDegreeOrdinaryStep.genRank_le_ceiling
      J block D (.alternating 5 (by decide)) (by trivial) eModel i hbelow

end SymmetricSubgroupAsymptotics.OriginalNonaffineBoundedHeadSmallLocalOrdinaryStep
