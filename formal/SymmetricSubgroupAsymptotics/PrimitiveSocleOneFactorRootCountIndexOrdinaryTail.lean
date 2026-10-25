import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorRootStarOrdinaryTail

/-! A literal finite root-generator count at most four times the
prime-field index dimension pays the ordinary one-factor tail. The
prime power regrouped inside the proof is arithmetic bookkeeping only:
no action over that regrouped field, or new group model, is asserted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorRootCountIndexOrdinaryTail
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_linear_log (hk : D.factorCount = 1)
    (q : CFSG.PrimePower) (r : ℕ) (hr : 0 < r)
    (S : Finset D.Simple) (hS : Subgroup.closure (S : Set D.Simple) = ⊤)
    (hcard : S.card ≤ 4 * (q.exponent * r))
    (hindex : ∀ H : Subgroup D.Simple, H ≠ ⊤ → q.order ^ r ≤ H.index)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    (MarkedC4.genRank G : ℝ) ≤ 5 * Real.logb 2 (Nat.card X : ℝ) + 3 := by
  let q' : CFSG.PrimePower :=
    { prime := q.prime, exponent := q.exponent * r,
      prime_isPrime := q.prime_isPrime, exponent_pos := Nat.mul_pos q.exponent_pos hr }
  have hcard' : S.card ≤ (2 * 2) * q'.exponent := hcard
  have hindex' : ∀ H : Subgroup D.Simple, H ≠ ⊤ → q'.order ^ (2-1) ≤ H.index := by
    intro H hH
    simpa only [q', CFSG.PrimePower.order, show (2 : ℕ)-1 = 1 by decide,
      pow_one, pow_mul] using hindex H hH
  exact PrimitiveSocleOneFactorRootStarOrdinaryTail.genRank_le_linear_log
    D hk q' 2 (by decide) S hS hcard' hindex' ell hell houter

theorem genRank_le_ceiling (hk : D.factorCount = 1)
    (q : CFSG.PrimePower) (r : ℕ) (hr : 0 < r)
    (S : Finset D.Simple) (hS : Subgroup.closure (S : Set D.Simple) = ⊤)
    (hcard : S.card ≤ 4 * (q.exponent * r))
    (hindex : ∀ H : Subgroup D.Simple, H ≠ ⊤ → q.order ^ r ≤ H.index)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)))
    (hn : 128 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  have hh := genRank_le_linear_log D hk q r hr S hS hcard hindex ell hell houter
  have hreal := (hh.trans (LinearLogOrdinaryGeneratorTail.aggregate_le (Nat.card X) hn)).trans
    (Nat.le_ceil ((Nat.card X : ℝ)/Real.sqrt (Real.logb 2 (Nat.card X : ℝ))))
  change (MarkedC4.genRank G : ℝ) ≤
    (traceyPermutationGeneratorCeiling (Nat.card X) : ℝ) at hreal
  exact_mod_cast hreal

theorem exists_generating_finset (hk : D.factorCount = 1)
    (q : CFSG.PrimePower) (r : ℕ) (hr : 0 < r)
    (S : Finset D.Simple) (hS : Subgroup.closure (S : Set D.Simple) = ⊤)
    (hcard : S.card ≤ 4 * (q.exponent * r))
    (hindex : ∀ H : Subgroup D.Simple, H ≠ ⊤ → q.order ^ r ≤ H.index)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)))
    (hn : 128 ≤ Nat.card X) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U, hU, hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U, hgen, hU.le.trans
    (genRank_le_ceiling D hk q r hr S hS hcard hindex ell hell houter hn)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorRootCountIndexOrdinaryTail
