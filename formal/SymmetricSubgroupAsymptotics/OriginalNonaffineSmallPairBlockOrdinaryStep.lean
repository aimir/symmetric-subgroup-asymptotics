import SymmetricSubgroupAsymptotics.OriginalNonaffineDisplayedPairBlockOrdinaryStep
import SymmetricSubgroupAsymptotics.PrimitiveSocleDegreeBelowTwentyFiveOuterMultiplicity
import SymmetricSubgroupAsymptotics.NonaffineOnePairSmallDegreeOrdinaryAggregate

/-! The actual one-factor pair band completes paired local degrees >=10.
The original source, full socle, local quotient and inherited top are the
same throughout. A genuinely ONE pair head is retained below degree 25. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineSmallPairBlockOrdinaryStep
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

/-- The ONE-factor geometry pays one actual pair, not an independent
worst-case pair for each putative minimal normal subgroup. -/
theorem genRank_le_ceiling_of_degree_band (i : block.Points)
    (hr : 10 ≤ Nat.card block.Fibre) (hsmall : Nat.card block.Fibre < 25)
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
  obtain ⟨hk,hout⟩ := PrimitiveSocleDegreeBelowTwentyFiveOuterMultiplicity.factor_and_outer_multiplicity
    D hsmall ell hell horder houter
  have hb : (B : ℝ) ≤ 3 := by
    dsimp only [B]
    simpa only [hk,Nat.one_mul,Nat.factorial_one,ArithmeticFunction.cardFactors_one,Nat.add_zero]
      using (show (ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) : ℝ) ≤ 3 by exact_mod_cast hout)
  have ht : 2 ≤ t := block.degrees_ge_two.2
  have hsimple : MarkedC4.genRank D.Simple ≤ 2 := (MarkedC4.genRank_le hS).trans hcard
  have hs : (MarkedC4.genRank D.Simple : ℝ) ≤ 2 := by exact_mod_cast hsimple
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
  have hreal := hcost.trans (NonaffineOnePairSmallDegreeOrdinaryAggregate.one_pair_cost_le
    r t hr hsmall ht B (by positivity) hb)
  have hproduct : r*t = n := by simpa only [Nat.card_fin] using block.degree_product
  have hproductR : (r : ℝ)*(t : ℝ) = (n : ℝ) := by exact_mod_cast hproduct
  simp only [hproductR] at hreal
  have hh := hreal.trans (Nat.le_ceil ((n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ))))
  change (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling n : ℝ) at hh
  exact_mod_cast hh

theorem genRank_le_ceiling (i : block.Points) (hr : 10 ≤ Nat.card block.Fibre)
    (S : Finset D.Simple) (hS : Subgroup.closure (S : Set D.Simple) = ⊤) (hcard : S.card ≤ 2)
    (hbelow : SmallerTransitiveRankBound n)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (horder : ell^2 < Nat.card D.Simple)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  by_cases hlarge : 25 ≤ Nat.card block.Fibre
  · exact OriginalNonaffineDisplayedPairBlockOrdinaryStep.genRank_le_ceiling
      J block D i hlarge S hS hcard hbelow ell hell horder houter
  · exact genRank_le_ceiling_of_degree_band J block D i hr (by omega)
      S hS hcard hbelow ell hell horder houter

theorem exists_generating_finset (i : block.Points) (hr : 10 ≤ Nat.card block.Fibre)
    (S : Finset D.Simple) (hS : Subgroup.closure (S : Set D.Simple) = ⊤) (hcard : S.card ≤ 2)
    (hbelow : SmallerTransitiveRankBound n)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (horder : ell^2 < Nat.card D.Simple)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    ∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧
      F.card ≤ traceyPermutationGeneratorCeiling n := by
  obtain ⟨F,hF,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨F,hgen,hF.le.trans (genRank_le_ceiling J block D i hr
    S hS hcard hbelow ell hell horder houter)⟩

theorem genRank_le_ceiling_of_model {M : Type} [Group M] (e : D.Simple ≃* M)
    (hpair : ∃ S : Finset M, Subgroup.closure (S : Set M) = ⊤ ∧ S.card ≤ 2)
    (hpacket : ∀ ell : ℕ, LeastProperIndex M ell →
      ell^2 < Nat.card M ∧ SufficientOuterOrderBudget ell (Nat.card (Outer M)))
    (i : block.Points) (hr : 10 ≤ Nat.card block.Fibre)
    (hbelow : SmallerTransitiveRankBound n) :
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
  exact genRank_le_ceiling J block D i hr U hU hUcard hbelow ell hell horder houter

end SymmetricSubgroupAsymptotics.OriginalNonaffineSmallPairBlockOrdinaryStep
