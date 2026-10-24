import SymmetricSubgroupAsymptotics.OriginalBinaryAffineArbitraryTopOrdinaryStep
import SymmetricSubgroupAsymptotics.TraceyStrictlySmallerTransitiveActions

/-! The original binary affine local-component branch of independent
strong induction for the coarse Tracey ceiling. The actual top degree is
strictly smaller by the genuine minimal-block geometry; its ceiling is
derived from the literal subgroup IH, not a global Tracey/MN theorem.
Primitive actions and odd/nonaffine local components remain separate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineCoarseDegreeInduction
open TraceyStrictlySmallerTransitiveActions

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

theorem top_genRank_le (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling (Nat.card block.Points) := by
  letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
  exact rank_of_faithful_transitive_action n hbelow block.Top block.Points
    block.degrees_ge_two.2 (by simpa only [Nat.card_fin] using block.degrees_lt.2)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_ceiling (hp : P.p = 2) (i : block.Points)
    (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n :=
  OriginalBinaryAffineArbitraryTopOrdinaryStep.genRank_le_ceiling J block P hp i
    (top_genRank_le J block hbelow)

theorem exists_generating_finset_of_smaller_subgroups (hp : P.p = 2) (i : block.Points)
    (hbelow : ∀ (k : ℕ), k < n → ∀ K : Subgroup (Equiv.Perm (Fin k)), 2 ≤ k →
      MulAction.IsPretransitive K (Fin k) →
        ∃ S : Finset K, Subgroup.closure (S : Set K) = ⊤ ∧
          S.card ≤ traceyPermutationGeneratorCeiling k) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling n := by
  exact OriginalBinaryAffineArbitraryTopOrdinaryStep.exists_generating_finset J block P hp i
    (top_genRank_le J block (of_subgroup_generators n hbelow))

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineCoarseDegreeInduction
