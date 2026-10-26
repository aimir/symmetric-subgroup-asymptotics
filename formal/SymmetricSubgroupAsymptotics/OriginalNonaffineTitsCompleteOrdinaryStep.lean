import SymmetricSubgroupAsymptotics.PrimitiveSocleTitsActualOrdinaryPacket
import SymmetricSubgroupAsymptotics.NonaffineFourHeadTwoOuterSmallLocalOrdinaryAggregate
import SymmetricSubgroupAsymptotics.OriginalNonaffineThirtyTwoOrdinaryStep

/-! Every actual Tits original nonaffine block row. The same original
compression state, component, fibres and top remain literal. Only
strict-smaller TRANSITIVE induction is retained; all Tits numerical and
ordinary-generation facts are supplied internally. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineTitsCompleteOrdinaryStep
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open OriginalBlockOrdinaryCompressionState ActualWreathChiefUnitMinimumRate
open ActualWreathPrimitiveSocleOuterOrdinaryCost

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A:=J) x₀) [Fintype block.Points]

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
    (e : D.Simple ≃* CFSG.Index.tits.Model) (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  obtain ⟨horder,houter⟩ := PrimitiveSocleTitsActualOrdinaryPacket.packet D e ell hell
  by_cases h32 : 32 ≤ Nat.card block.Fibre
  · exact OriginalNonaffineThirtyTwoOrdinaryStep.genRank_le_ceiling_of_actual_packet
      J block D i h32 hbelow ell hell horder houter
  have hsmall : Nat.card block.Fibre < 32 := by omega
  have h14 := PrimitiveSocleTitsActualOrdinaryPacket.least_index_fourteen_le D e ell hell
  have hdegree := primitiveSocle_power_le_degree (by omega : 5 ≤ ell) horder (D.degreeForm hell)
  have hk : D.factorCount=1 := by
    by_contra hne
    have hk2 : 2 ≤ D.factorCount := by have hp := D.factorCount_pos; omega
    have hp := (Nat.pow_le_pow_right (by omega : 0 < ell) hk2).trans hdegree
    nlinarith only [hp,h14,hsmall]
  let r := Nat.card block.Fibre
  let t := Nat.card block.Points
  let B := ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))
  have hr : 14 ≤ r := h14.trans
    (PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell)
  have ht : 2 ≤ t := block.degrees_ge_two.2
  have hsimple := PrimitiveSocleTitsActualOrdinaryPacket.simple_genRank_le_four D e
  have hb := PrimitiveSocleTitsActualOrdinaryPacket.outer_cardFactors_le_two D e
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
  have hnum := NonaffineFourHeadTwoOuterSmallLocalOrdinaryAggregate.cost_le
    r t hr hsmall ht (MarkedC4.genRank D.Simple) B (by positivity)
    (by exact_mod_cast hsimple) (by positivity) (by exact_mod_cast hb)
  have hreal := hcost.trans hnum
  have hproduct : r*t=n := by simpa only [Nat.card_fin] using block.degree_product
  have hproductR : (r : ℝ)*(t : ℝ)=(n : ℝ) := by exact_mod_cast hproduct
  rw [hproductR] at hreal
  have hh := hreal.trans (Nat.le_ceil ((n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ))))
  change (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling n : ℝ) at hh
  exact_mod_cast hh

theorem exists_generating_finset (i : block.Points)
    (e : D.Simple ≃* CFSG.Index.tits.Model) (hbelow : SmallerTransitiveRankBound n) :
    ∃ S : Finset J, Subgroup.closure (S : Set J)=⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling n := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=J)
  exact ⟨S,hgen,hS.le.trans (genRank_le_ceiling J block D i e hbelow)⟩

end SymmetricSubgroupAsymptotics.OriginalNonaffineTitsCompleteOrdinaryStep
