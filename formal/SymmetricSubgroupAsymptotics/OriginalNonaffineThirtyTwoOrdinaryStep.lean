import SymmetricSubgroupAsymptotics.OriginalNonaffineMinimumRateOrdinaryStep
import SymmetricSubgroupAsymptotics.NonaffineSmallDegreeOneHeadOrdinaryAggregate
import SymmetricSubgroupAsymptotics.PrimitiveSocleSmallDegreeMultipleHeadParameters
import SymmetricSubgroupAsymptotics.NonaffineSmallDegreeMultipleHeadOrdinaryAggregate

/-! Original nonaffine imprimitive ordinary induction at LOCAL degree>=32.
All original coordinates, full-socle charts and quotient trace remain the
same. Only strictly smaller TRANSITIVE coset/top induction is used.
Neither pair nor root-generation hypotheses are needed. Exact model
packets are filled internally; Tits/sporadic witnesses remain literal. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineThirtyTwoOrdinaryStep
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open OriginalNonaffineBlockSocleOrdinaryCost
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (D : NonaffineData block.Component block.Fibre)

theorem genRank_le_ceiling_of_actual_packet (i : block.Points)
    (hr : 32 ≤ Nat.card block.Fibre) (hbelow : SmallerTransitiveRankBound n)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (horder : ell^2 < Nat.card D.Simple)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  by_cases hlarge : 128 ≤ Nat.card block.Fibre
  · exact OriginalNonaffineMinimumRateOrdinaryStep.genRank_le_ceiling_of_actual_packet
      J block D i hlarge hbelow ell hell horder houter
  have hsmall : Nat.card block.Fibre < 128 := by omega
  let r := Nat.card block.Fibre
  let t := Nat.card block.Points
  let L := Real.logb 2 (r : ℝ)
  let B := D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
    ArithmeticFunction.cardFactors D.factorCount.factorial
  have ht : 2 ≤ t := block.degrees_ge_two.2
  have hell2 : 2 ≤ ell := by
    obtain ⟨H,hH,hindex⟩ := hell.1
    have hh := H.one_lt_index_of_ne_top hH
    omega
  have hellr : ell ≤ r := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hB0 : (0 : ℝ) ≤ B := by positivity
  have hsource := genRank_le_strict_coset_cost J block D i ell hell hbelow
  change (MarkedC4.genRank J : ℝ) ≤ 2*(traceyPermutationGeneratorCeiling ell : ℝ)+
    (B : ℝ)*ActualWreathChiefUnitMinimumRate.rate t+traceyPermutationGeneratorCeiling t at hsource
  have hreal : (MarkedC4.genRank J : ℝ) ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
    by_cases hk : D.factorCount = 1
    · have hone := genRank_le_one_factor_strict_coset_cost J block D i ell hell hk hbelow
      change (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling ell : ℝ)+
        (B : ℝ)*ActualWreathChiefUnitMinimumRate.rate t+traceyPermutationGeneratorCeiling t at hone
      have hlinear := PrimitiveSocleOuterMultiplicityDegreeBounds.multiplicity_le_linear_log_of_one_factor
        D hk ell hell houter
      change (B : ℝ) ≤ 3+L at hlinear
      exact hone.trans (NonaffineSmallDegreeOneHeadOrdinaryAggregate.one_factor_cost_le
        r t ell hr hsmall ht hell2 hellr B hB0 hlinear)
    · have hk2 : 2 ≤ D.factorCount := by have hp := D.factorCount_pos; omega
      rcases PrimitiveSocleSmallDegreeMultipleHeadParameters.parameters
        D hr hsmall hk2 ell hell horder houter with ⟨hr64,hhead,hB⟩ | ⟨hr64,hhead,hB⟩
      · have hheadR : (traceyPermutationGeneratorCeiling ell : ℝ) ≤ 5 := by exact_mod_cast hhead
        have hBR : (B : ℝ) ≤ 7 := by exact_mod_cast hB
        have hcost : (MarkedC4.genRank J : ℝ) ≤ 10+
            (B : ℝ)*ActualWreathChiefUnitMinimumRate.rate t+traceyPermutationGeneratorCeiling t := by
          linarith only [hsource,hheadR]
        exact hcost.trans (NonaffineSmallDegreeMultipleHeadOrdinaryAggregate.low_band_cost_le
          r t hr hr64 ht 10 B (by norm_num) (le_refl _) hB0 hBR)
      · have hheadR : (traceyPermutationGeneratorCeiling ell : ℝ) ≤ 6 := by exact_mod_cast hhead
        have hBR : (B : ℝ) ≤ 11 := by exact_mod_cast hB
        have hcost : (MarkedC4.genRank J : ℝ) ≤ 12+
            (B : ℝ)*ActualWreathChiefUnitMinimumRate.rate t+traceyPermutationGeneratorCeiling t := by
          linarith only [hsource,hheadR]
        exact hcost.trans (NonaffineSmallDegreeMultipleHeadOrdinaryAggregate.high_band_cost_le
          r t hr64 hsmall ht 12 B (by norm_num) (le_refl _) hB0 hBR)
  have hproduct : r*t = n := by simpa only [Nat.card_fin] using block.degree_product
  have hproductR : (r : ℝ)*(t : ℝ) = (n : ℝ) := by exact_mod_cast hproduct
  simp only [hproductR] at hreal
  have hh := hreal.trans (Nat.le_ceil ((n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ))))
  change (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling n : ℝ) at hh
  exact_mod_cast hh

/-- The final degree32 reduction supplies every available model packet
itself. Only the literal remaining model tag and SAME factor equivalence
are returned; no user callback on models is added. -/
theorem genRank_le_ceiling_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (i : block.Points) (hr : 32 ≤ Nat.card block.Fibre)
    (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases CFSGSimpleIndexPacketOrTitsSporadic.factor_packet_or_actual_remaining_model D hCFSG with
    hpacket | hremaining
  · obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
    obtain ⟨horder,houter⟩ := hpacket ell hell
    exact Or.inl (genRank_le_ceiling_of_actual_packet J block D i hr hbelow ell hell horder houter)
  · exact Or.inr hremaining

theorem exists_generating_finset_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (i : block.Points) (hr : 32 ≤ Nat.card block.Fibre)
    (hbelow : SmallerTransitiveRankBound n) :
    (∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧
      F.card ≤ traceyPermutationGeneratorCeiling n) ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases genRank_le_ceiling_or_actual_remaining_model J block D hCFSG i hr hbelow with h | h
  · obtain ⟨F,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨F,hgen,hcard.le.trans h⟩
  · exact Or.inr h

end SymmetricSubgroupAsymptotics.OriginalNonaffineThirtyTwoOrdinaryStep
