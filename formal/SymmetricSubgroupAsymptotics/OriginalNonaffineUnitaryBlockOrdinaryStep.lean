import SymmetricSubgroupAsymptotics.OriginalNonaffineSmallUnitaryBlockOrdinaryStep
import SymmetricSubgroupAsymptotics.CFSGUnitaryBinaryRankThreeFrattiniHead
import SymmetricSubgroupAsymptotics.NonaffineFourGeneratorEightDegreeOrdinaryAggregate

/-! Whole original unitary imprimitive ordinary induction. The sole
small binary rank-three state uses its actual Frattini-shear head4 and
actual outer cardinal2. All other states are supplied by the previously
checked original unitary reduction; only strictly smaller TRANSITIVE
ordinary bounds are used, with the SAME source, socle and top. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineUnitaryBlockOrdinaryStep
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

theorem genRank_le_ceiling (rank : ℕ) (q : CFSG.PrimePower)
    (hrank : 2 ≤ rank) (hs : rank = 2 → q.order ≠ 2)
    (e : D.Simple ≃* CFSG.Models.TwistedA rank q) (i : block.Points)
    (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  rcases OriginalNonaffineSmallUnitaryBlockOrdinaryStep.genRank_le_ceiling_or_binary_rank_three
    J block D rank q hrank hs e i hbelow with h | ⟨hr3,hq2,hsmall⟩
  · exact h
  subst rank
  letI : IsSimpleGroup (CFSG.Models.TwistedA 3 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedA 3 q) := Finite.of_equiv D.Simple e.toEquiv
  have hn : ¬ IsMulCommutative (CFSG.Models.TwistedA 3 q) := by
    intro h
    exact D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr h)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hm := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  have horder : ell^2 < Nat.card D.Simple := by
    simpa only [Nat.card_congr e.toEquiv] using
      CFSGTwistedAUnitaryCoordinates.twistedA_admissible_leastIndex_square_lt 3 (by omega) q
        (by omega) ell hm
  have hfield := CFSGTwistedAUnitaryCoordinates.twistedA_admissible_order_power_le_leastProperIndex
    3 (by omega) q (by omega) ell hm
  have hell8 : 8 ≤ ell := by simpa only [hq2] using hfield
  have hr8 := hell8.trans (PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell)
  have hdegree := primitiveSocle_power_le_degree (show 5 ≤ ell by omega) horder (D.degreeForm hell)
  have hk : D.factorCount = 1 := by
    have hp := D.factorCount_pos
    by_contra hh
    have hpow := (Nat.pow_le_pow_right (show 0 < ell by omega)
      (show 2 ≤ D.factorCount by omega)).trans hdegree
    have h64 := Nat.pow_le_pow_left hell8 2
    norm_num at h64
    omega
  have hhead : MarkedC4.genRank D.Simple ≤ 4 := by
    rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e]
    exact CFSGUnitaryBinaryRankThreeFrattiniHead.model_genRank_le_four q hq2
  have hcard : Nat.card (Outer D.Simple) ≤ 2 := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGUnitaryCoprimeOuterCardinality.binary_rank_three_or_four_outer_card_le_two
      q hq2 0 (Or.inl rfl) hn
  have hout : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 1 :=
    SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow _ 1 Nat.card_pos (by omega)
  let r := Nat.card block.Fibre
  let t := Nat.card block.Points
  have hc0 := source_head_cost J block D i hk 4 1 hhead hout hbelow
  have hc : (MarkedC4.genRank J : ℝ) ≤ 4+1*rate t+traceyPermutationGeneratorCeiling t := by
    simpa only [Nat.cast_ofNat,Nat.cast_one] using hc0
  have hreal := hc.trans (NonaffineFourGeneratorEightDegreeOrdinaryAggregate.cost_le r t
    hr8 hsmall block.degrees_ge_two.2 4 1
    (by norm_num) (le_refl _) (by norm_num) (le_refl _))
  have hproduct : r*t = n := by simpa only [Nat.card_fin] using block.degree_product
  have hproductR : (r : ℝ)*(t : ℝ) = (n : ℝ) := by exact_mod_cast hproduct
  simp only [hproductR] at hreal
  have hh := hreal.trans (Nat.le_ceil ((n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ))))
  change (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling n : ℝ) at hh
  exact_mod_cast hh

theorem exists_generating_finset (rank : ℕ) (q : CFSG.PrimePower)
    (hrank : 2 ≤ rank) (hs : rank = 2 → q.order ≠ 2)
    (e : D.Simple ≃* CFSG.Models.TwistedA rank q) (i : block.Points)
    (hbelow : SmallerTransitiveRankBound n) :
    ∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧
      F.card ≤ traceyPermutationGeneratorCeiling n := by
  obtain ⟨F,hF,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨F,hgen,hF.le.trans (genRank_le_ceiling J block D rank q hrank hs e i hbelow)⟩

end SymmetricSubgroupAsymptotics.OriginalNonaffineUnitaryBlockOrdinaryStep
