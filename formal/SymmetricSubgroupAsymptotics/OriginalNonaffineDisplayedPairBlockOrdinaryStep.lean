import SymmetricSubgroupAsymptotics.OriginalNonaffineLargeFibreOrdinaryStep
import SymmetricSubgroupAsymptotics.PrimitiveSocleSmallDegreeOuterMultiplicity
import SymmetricSubgroupAsymptotics.NonaffineDisplayedPairsOrdinaryAggregate

/-! Original imprimitive actions with an actual pair in the simple factor.
The local socle and its original quotient stay correlated. For local
sizes 25 through 1023 the actual outer multiplicity has a twice-log bound;
larger sizes reuse strict-coset induction. Only the strictly smaller
TRANSITIVE induction hypothesis is used, never global Tracey or MN. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineDisplayedPairBlockOrdinaryStep
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open OriginalNonaffineBlockSocleOrdinaryCost

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (D : NonaffineData block.Component block.Fibre)

/-- Bounded local sizes are paid by literal pair generators, the SAME
outer coefficient, and induction only on the actual original top. -/
theorem genRank_le_ceiling_of_small_degree (i : block.Points)
    (hr : 25 ≤ Nat.card block.Fibre) (hsmall : Nat.card block.Fibre < 1024)
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
  have ht : 2 ≤ t := block.degrees_ge_two.2
  have hsimple : MarkedC4.genRank D.Simple ≤ 2 := (MarkedC4.genRank_le hS).trans hcard
  have hs : (MarkedC4.genRank D.Simple : ℝ) ≤ 2 := by exact_mod_cast hsimple
  have htop : (MarkedC4.genRank block.Top : ℝ) ≤ traceyPermutationGeneratorCeiling t := by
    letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
    have hh := rank_of_faithful_transitive_action n hbelow block.Top block.Points
      block.degrees_ge_two.2 (by simpa only [Nat.card_fin] using block.degrees_lt.2)
    exact_mod_cast hh
  have hsource := source_genRank_le_socle_cost J block D i
  change (MarkedC4.genRank J : ℝ) ≤ 2*(MarkedC4.genRank D.Simple : ℝ)+
    (B : ℝ)*ActualWreathChiefUnitMinimumRate.rate t+MarkedC4.genRank block.Top at hsource
  have hb := PrimitiveSocleSmallDegreeOuterMultiplicity.multiplicity_le_twice_log_of_small_degree
    D hr hsmall ell hell horder houter
  change (B : ℝ) ≤ 2*Real.logb 2 (r : ℝ) at hb
  have hcost : (MarkedC4.genRank J : ℝ) ≤
      4+(B : ℝ)*ActualWreathChiefUnitMinimumRate.rate t+traceyPermutationGeneratorCeiling t := by
    linarith only [hsource,hs,htop]
  have hreal := hcost.trans (NonaffineDisplayedPairsOrdinaryAggregate.two_pair_cost_le
    r t hr ht B (by positivity) hb)
  have hproduct : r*t = n := by simpa only [Nat.card_fin] using block.degree_product
  have hproductR : (r : ℝ)*(t : ℝ) = (n : ℝ) := by exact_mod_cast hproduct
  simp only [hproductR] at hreal
  have hh := hreal.trans (Nat.le_ceil ((n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ))))
  change (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling n : ℝ) at hh
  exact_mod_cast hh

/-- Every local degree at least 25 is covered, retaining the actual pair
and actual index/outer packet rather than an assumed simple-rank bound. -/
theorem genRank_le_ceiling (i : block.Points) (hr : 25 ≤ Nat.card block.Fibre)
    (S : Finset D.Simple) (hS : Subgroup.closure (S : Set D.Simple) = ⊤) (hcard : S.card ≤ 2)
    (hbelow : SmallerTransitiveRankBound n)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (horder : ell^2 < Nat.card D.Simple)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  by_cases hlarge : 1024 ≤ Nat.card block.Fibre
  · exact OriginalNonaffineLargeFibreOrdinaryStep.genRank_le_ceiling_of_actual_packet
      J block D i hlarge hbelow ell hell horder houter
  · exact genRank_le_ceiling_of_small_degree J block D i hr (by omega)
      S hS hcard hbelow ell hell horder houter

theorem exists_generating_finset (i : block.Points) (hr : 25 ≤ Nat.card block.Fibre)
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

/-- Transport of a literal model pair and SAME-model packet. Final family
consumers supply both from their existing proved model theorems. -/
theorem genRank_le_ceiling_of_model {M : Type} [Group M] (e : D.Simple ≃* M)
    (hpair : ∃ S : Finset M, Subgroup.closure (S : Set M) = ⊤ ∧ S.card ≤ 2)
    (hpacket : ∀ ell : ℕ, LeastProperIndex M ell →
      ell^2 < Nat.card M ∧ SufficientOuterOrderBudget ell (Nat.card (Outer M)))
    (i : block.Points) (hr : 25 ≤ Nat.card block.Fibre)
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

end SymmetricSubgroupAsymptotics.OriginalNonaffineDisplayedPairBlockOrdinaryStep
