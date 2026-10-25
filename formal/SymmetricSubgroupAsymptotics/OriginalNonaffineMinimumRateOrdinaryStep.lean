import SymmetricSubgroupAsymptotics.OriginalNonaffineLargeFibreOrdinaryStep
import SymmetricSubgroupAsymptotics.PrimitiveSocleSmallDegreeOuterMultiplicity
import SymmetricSubgroupAsymptotics.NonaffineStrictCosetMinimumRateTail

/-! Original nonaffine imprimitive ordinary induction at local degree>=128.
No root- or pair-generation hypothesis is needed: the SAME actual least
index supplies genuine strict-smaller transitive coset induction, and the
full-socle ONE/two-head split is retained. Both actual induced rates pay
the original correlated local quotient and actual rounded top ceiling.
CFSG supplies all alternating/Lie packets internally; exact Tits/sporadic
factor witnesses remain explicit. This is not a global Tracey proof. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineMinimumRateOrdinaryStep
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open OriginalNonaffineBlockSocleOrdinaryCost
open NonaffineStrictCosetMinimumRateTail
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (D : NonaffineData block.Component block.Fibre)

theorem genRank_le_ceiling_of_actual_packet (i : block.Points)
    (hr : 128 ≤ Nat.card block.Fibre) (hbelow : SmallerTransitiveRankBound n)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (horder : ell^2 < Nat.card D.Simple)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  by_cases hlarge : 1024 ≤ Nat.card block.Fibre
  · exact OriginalNonaffineLargeFibreOrdinaryStep.genRank_le_ceiling_of_actual_packet
      J block D i hlarge hbelow ell hell horder houter
  have hsmall : Nat.card block.Fibre < 1024 := by omega
  let r := Nat.card block.Fibre
  let t := Nat.card block.Points
  let L := Real.logb 2 (r : ℝ)
  let B := D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
    ArithmeticFunction.cardFactors D.factorCount.factorial
  have ht : 2 ≤ t := block.degrees_ge_two.2
  have hell5 : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  have hell2 : 2 ≤ ell := by omega
  have hellr : ell ≤ r := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hdegree : ell^D.factorCount ≤ r :=
    primitiveSocle_power_le_degree hell5 horder (D.degreeForm hell)
  have hB0 : (0 : ℝ) ≤ B := by positivity
  have hBsmall := PrimitiveSocleSmallDegreeOuterMultiplicity.multiplicity_le_twice_log_of_small_degree
    D (by omega) hsmall ell hell horder houter
  change (B : ℝ) ≤ 2*L at hBsmall
  have hsource := genRank_le_strict_coset_cost J block D i ell hell hbelow
  change (MarkedC4.genRank J : ℝ) ≤ 2*(traceyPermutationGeneratorCeiling ell : ℝ)+
    (B : ℝ)*ActualWreathChiefUnitMinimumRate.rate t+traceyPermutationGeneratorCeiling t at hsource
  have hreal : (MarkedC4.genRank J : ℝ) ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
    by_cases hs : ell^2 ≤ r
    · have hceilNat := PrimitiveSocleProductIndexOrdinaryCost.ceiling_le_degree ell hell2
      have hceil : (traceyPermutationGeneratorCeiling ell : ℝ) ≤ ell := by exact_mod_cast hceilNat
      have hsqrt : (ell : ℝ) ≤ Real.sqrt (r : ℝ) :=
        (Real.le_sqrt (by positivity) (by positivity)).mpr (by exact_mod_cast hs)
      have hhead := hceil.trans hsqrt
      have hbound : (MarkedC4.genRank J : ℝ) ≤ 2*Real.sqrt (r : ℝ)+
          (B : ℝ)*ActualWreathChiefUnitMinimumRate.rate t+traceyPermutationGeneratorCeiling t := by
        linarith only [hsource,hhead]
      exact hbound.trans (square_root_cost_le r t hr ht B hB0 hBsmall)
    · have hk : D.factorCount = 1 := by
        have hpos := D.factorCount_pos
        by_contra hne
        have hk2 : 2 ≤ D.factorCount := by omega
        exact hs ((Nat.pow_le_pow_right (show 0 < ell by omega) hk2).trans hdegree)
      have hone := genRank_le_one_factor_strict_coset_cost J block D i ell hell hk hbelow
      change (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling ell : ℝ)+
        (B : ℝ)*ActualWreathChiefUnitMinimumRate.rate t+traceyPermutationGeneratorCeiling t at hone
      have hlinear := PrimitiveSocleOuterMultiplicityDegreeBounds.multiplicity_le_linear_log_of_one_factor
        D hk ell hell houter
      change (B : ℝ) ≤ 3+L at hlinear
      exact hone.trans (one_factor_cost_le r t ell hr ht hell2 hellr
        (by omega : r ≤ ell^2) B hB0 hlinear)
  have hproduct : r*t = n := by simpa only [Nat.card_fin] using block.degree_product
  have hproductR : (r : ℝ)*(t : ℝ) = (n : ℝ) := by exact_mod_cast hproduct
  simp only [hproductR] at hreal
  have hh := hreal.trans (Nat.le_ceil ((n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ))))
  change (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling n : ℝ) at hh
  exact_mod_cast hh

/-- The final minimum-rate reduction supplies every available model packet
itself. Only the literal remaining model tag and SAME factor equivalence
are returned; no user callback on models is added. -/
theorem genRank_le_ceiling_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (i : block.Points) (hr : 128 ≤ Nat.card block.Fibre)
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
    (i : block.Points) (hr : 128 ≤ Nat.card block.Fibre)
    (hbelow : SmallerTransitiveRankBound n) :
    (∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧
      F.card ≤ traceyPermutationGeneratorCeiling n) ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases genRank_le_ceiling_or_actual_remaining_model J block D hCFSG i hr hbelow with h | h
  · obtain ⟨F,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨F,hgen,hcard.le.trans h⟩
  · exact Or.inr h

end SymmetricSubgroupAsymptotics.OriginalNonaffineMinimumRateOrdinaryStep
