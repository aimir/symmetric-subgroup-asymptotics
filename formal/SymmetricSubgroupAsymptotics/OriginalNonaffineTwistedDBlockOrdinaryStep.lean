import SymmetricSubgroupAsymptotics.OriginalNonaffineThirtyTwoOrdinaryStep
import SymmetricSubgroupAsymptotics.NonaffineEightGeneratorSmallDegreeOrdinaryAggregate
import SymmetricSubgroupAsymptotics.TwistedDPointRadicalSmallDegreeParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedDPointRadicalIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGTwistedDOuterCardinality
import SymmetricSubgroupAsymptotics.ClassicalClassEquationSmallParameters

/-! Whole original nonsplit-D imprimitive ordinary induction. Above local
32 the strict-coset packet is used. Below32 the actual point-radical
index forces rank4 and the binary field; SAME-model root generation and
outer cardinality pay a genuine eight-generator head. No pair premise,
finite action catalogue or current-degree permutation bound is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineTwistedDBlockOrdinaryStep
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

private theorem small_degree_cost (i : block.Points)
    (hr : 24 ≤ Nat.card block.Fibre) (hsmall : Nat.card block.Fibre < 32)
    (hk : D.factorCount = 1) (hhead : MarkedC4.genRank D.Simple ≤ 8)
    (hout : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 3)
    (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let r := Nat.card block.Fibre
  let t := Nat.card block.Points
  let B := D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
    ArithmeticFunction.cardFactors D.factorCount.factorial
  have hb : (B : ℝ) ≤ 3 := by
    dsimp only [B]
    simpa only [hk,Nat.one_mul,Nat.factorial_one,ArithmeticFunction.cardFactors_one,Nat.add_zero]
      using (show (ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) : ℝ) ≤ 3 by exact_mod_cast hout)
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
  have hs : (MarkedC4.genRank D.Simple : ℝ) ≤ 8 := by exact_mod_cast hhead
  have hcost : (MarkedC4.genRank J : ℝ) ≤ 8+(B : ℝ)*rate t+traceyPermutationGeneratorCeiling t := by
    linarith only [hsource,hs,htop]
  have hreal := hcost.trans (NonaffineEightGeneratorSmallDegreeOrdinaryAggregate.eight_generator_cost_le
    r t hr hsmall block.degrees_ge_two.2 8 B (by norm_num) (le_refl _) (by positivity) hb)
  have hproduct : r*t = n := by simpa only [Nat.card_fin] using block.degree_product
  have hproductR : (r : ℝ)*(t : ℝ) = (n : ℝ) := by exact_mod_cast hproduct
  simp only [hproductR] at hreal
  have hh := hreal.trans (Nat.le_ceil ((n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ))))
  change (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling n : ℝ) at hh
  exact_mod_cast hh

/-- The rank, field, original model and factor equivalence remain literal
through the small-degree reduction and the ordinary source bound. -/
theorem genRank_le_ceiling (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedD r q) (i : block.Points)
    (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  classical
  obtain ⟨s,rfl⟩ : ∃ s : ℕ, r = s+4 := ⟨r-4,by omega⟩
  letI : IsSimpleGroup (CFSG.Models.TwistedD (s+4) q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedD (s+4) q) := Finite.of_equiv D.Simple e.toEquiv
  have hn : ¬ IsMulCommutative (CFSG.Models.TwistedD (s+4) q) := by
    intro h
    exact D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr h)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hm := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  have horder : ell^2 < Nat.card D.Simple := by
    simpa only [Nat.card_congr e.toEquiv] using
      CFSGReduction.typeTwistedD_leastProperIndex_square_lt_card (s+4) q (by omega) ell hm
  have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGReduction.typeTwistedD_sufficientOuterBudget (s+4) (by omega) q hn ell hm
  by_cases hlarge : 32 ≤ Nat.card block.Fibre
  · exact OriginalNonaffineThirtyTwoOrdinaryStep.genRank_le_ceiling_of_actual_packet
      J block D i hlarge hbelow ell hell horder houter
  have hsmall : Nat.card block.Fibre < 32 := by omega
  have hellr := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hrad := CFSGReduction.typeTwistedD_point_radical_le_leastProperIndex
    (s+4) (by omega) q ell hm
  have hslice : (q.order^(s+2)-1)*q.order^(s+3) ≤ Nat.card block.Fibre := by
    have hh := hrad.trans hellr
    simpa only [show s+4-2 = s+2 by omega,show s+4-1 = s+3 by omega] using hh
  obtain ⟨hs,hq,hr24⟩ := TwistedDPointRadicalSmallDegreeParameters.parameters
    s q.order (Nat.card block.Fibre) (CFSGTwistedAQuadraticTrace.order_two_le q) hslice hsmall
  subst s
  have hell24 : 24 ≤ ell := by
    norm_num [hq] at hrad
    exact hrad
  have hell5 : 5 ≤ ell := by omega
  have hdegree := primitiveSocle_power_le_degree hell5 horder (D.degreeForm hell)
  have hk : D.factorCount = 1 := by
    have hp := D.factorCount_pos
    by_contra hh
    have hh2 : 2 ≤ D.factorCount := by omega
    have hpow := (Nat.pow_le_pow_right (show 0 < ell by omega) hh2).trans hdegree
    have h24 := Nat.pow_le_pow_left hell24 2
    norm_num at h24
    omega
  have he : q.exponent = 1 := ClassicalClassEquationCapacity.exponent_eq_one_of_prime_order
    q (by rw [hq]; decide)
  obtain ⟨S,hS,hcard⟩ := CFSGTwistedDRelativeOrdinaryGenerators.original_exists_generating_finset 0 q
  let U := S.image e.symm
  have hU : Subgroup.closure (U : Set D.Simple) = ⊤ := by
    rw [Finset.coe_image]
    change Subgroup.closure (e.symm.toMonoidHom '' (S : Set _)) = ⊤
    rw [← MonoidHom.map_closure,hS]
    exact Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hcard8 : S.card ≤ 8 := by simpa only [he] using hcard
  have hhead : MarkedC4.genRank D.Simple ≤ 8 :=
    (MarkedC4.genRank_le hU).trans (Finset.card_image_le.trans hcard8)
  have hout := CFSGTwistedDOuterCardinality.original_outer_card_le_eight_exponent 0 q hn
  have hout8 : Nat.card (Outer D.Simple) ≤ 8 := by
    rw [CFSGReduction.outer_card_congr e]
    simpa only [he,Nat.mul_one] using hout
  have hOmega : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 3 :=
    SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow _ 3 Nat.card_pos (by omega)
  exact small_degree_cost J block D i hr24 hsmall hk hhead hOmega hbelow

theorem exists_generating_finset (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedD r q) (i : block.Points)
    (hbelow : SmallerTransitiveRankBound n) :
    ∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧
      F.card ≤ traceyPermutationGeneratorCeiling n := by
  obtain ⟨F,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨F,hgen,hcard.le.trans (genRank_le_ceiling J block D r hr q e i hbelow)⟩

end SymmetricSubgroupAsymptotics.OriginalNonaffineTwistedDBlockOrdinaryStep
