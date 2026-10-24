import SymmetricSubgroupAsymptotics.PrimitiveSocleProductIndexOrdinaryTail

/-! The same actual ordinary tail for all multi-factor primitive degree
forms. The genuine index-square inequality is used only on the SAME
simple factor, to handle regular/diagonal degrees via the existing degree
form arithmetic. Almost-simple one-factor actions remain explicit.
No global simple-index, permutation-generator, or two-generation premise
is introduced: the two actual simple-factor bounds are stated locally. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleMultipleFactorOrdinaryTail
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (ell : ℕ)
    (hbelow : SmallerTransitiveRankBound (Nat.card X))
    (hell : LeastProperIndex D.Simple ell) (hk : 2 ≤ D.factorCount)
    (horder : ell^2 < Nat.card D.Simple) (hn : 1024 ≤ Nat.card X)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  have hell5 : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  have hpow : ell^D.factorCount ≤ Nat.card X :=
    primitiveSocle_power_le_degree hell5 horder (D.degreeForm hell)
  have hout : (Nat.card (Outer D.Simple) : ℝ) ≤
      6*Real.logb 2 (Nat.card D.Simple : ℝ) :=
    houter.log_six_of_le (by omega)
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
    (horder : ell^2 < Nat.card D.Simple) (hn : 1024 ≤ Nat.card X)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    ∃ s : Finset G, Subgroup.closure (s : Set G) = ⊤ ∧
      s.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨s,hs,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨s,hgen,hs.le.trans (genRank_le_ceiling D ell hbelow hell hk horder hn houter)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleMultipleFactorOrdinaryTail
