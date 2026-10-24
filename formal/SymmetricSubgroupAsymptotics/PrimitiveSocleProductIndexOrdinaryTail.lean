import SymmetricSubgroupAsymptotics.PrimitiveSocleProductIndexOrdinaryCost
import SymmetricSubgroupAsymptotics.PrimitiveProductOrdinaryRealTail
import SymmetricSubgroupAsymptotics.PrimitiveSocleLeastIndexDegreeComparison
import SymmetricSubgroupAsymptotics.CFSGSufficientSimpleIndexBounds

/-! A genuine product-index primitive ordinary-generator tail. The
actual full socle, simple type, and original faithful action are retained.
Only strictly-smaller TRANSITIVE induction is used. The explicit outer
budget is the existing model-level sufficient budget, not a global
permutation input. Regular/diagonal degree forms and the almost-simple
minimum-degree branch are not asserted here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleProductIndexOrdinaryTail
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (ell : ℕ)
    (hbelow : SmallerTransitiveRankBound (Nat.card X))
    (hell : LeastProperIndex D.Simple ell) (hk : 2 ≤ D.factorCount)
    (hproduct : ∃ H : Subgroup D.Simple,
      H ≠ ⊤ ∧ Nat.card X = H.index^D.factorCount)
    (hn : 1024 ≤ Nat.card X)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨H,hH,hdegree⟩ := hproduct
  have hpow : ell^D.factorCount ≤ Nat.card X := by
    rw [hdegree]
    exact Nat.pow_le_pow_left (hell.2 H hH) D.factorCount
  have hell0 : 0 < ell := by
    obtain ⟨K,hK,hindex⟩ := hell.1
    have hh := K.one_lt_index_of_ne_top hK
    omega
  have hout : (Nat.card (Outer D.Simple) : ℝ) ≤
      6*Real.logb 2 (Nat.card D.Simple : ℝ) :=
    houter.log_six_of_le hell0
      (PrimitiveSocleLeastIndexDegreeComparison.least_index_lt_order
        D.Simple D.noncommutative ell hell).le
  have hcost := PrimitiveSocleProductIndexOrdinaryCost.genRank_le_square_root_log_cost
    D (Nat.card X) ell hbelow hell hk hpow hout
  have htail := PrimitiveProductOrdinaryRealTail.aggregate_le (Nat.card X) hn
  have hreal := (hcost.trans htail).trans
    (Nat.le_ceil ((Nat.card X : ℝ)/Real.sqrt (Real.logb 2 (Nat.card X : ℝ))))
  change (MarkedC4.genRank G : ℝ) ≤
    (traceyPermutationGeneratorCeiling (Nat.card X) : ℝ) at hreal
  exact_mod_cast hreal

theorem exists_generating_finset (ell : ℕ)
    (hbelow : SmallerTransitiveRankBound (Nat.card X))
    (hell : LeastProperIndex D.Simple ell) (hk : 2 ≤ D.factorCount)
    (hproduct : ∃ H : Subgroup D.Simple,
      H ≠ ⊤ ∧ Nat.card X = H.index^D.factorCount)
    (hn : 1024 ≤ Nat.card X)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    ∃ s : Finset G, Subgroup.closure (s : Set G) = ⊤ ∧
      s.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨s,hs,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨s,hgen,hs.le.trans (genRank_le_ceiling D ell hbelow hell hk hproduct hn houter)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleProductIndexOrdinaryTail
