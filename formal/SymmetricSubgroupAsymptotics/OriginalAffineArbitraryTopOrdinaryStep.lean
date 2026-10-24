import SymmetricSubgroupAsymptotics.OriginalBinaryAffineArbitraryTopOrdinaryStep
import SymmetricSubgroupAsymptotics.OriginalOddAffineArbitraryTopOrdinaryStep

/-! The complete affine-component branch of independent coarse degree
induction. Every profile prime and every genuine top action is covered.
The only quantitative IH concerns strictly-smaller transitive actions;
the primitive and nonaffine branches are not asserted here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalAffineArbitraryTopOrdinaryStep
open TraceyStrictlySmallerTransitiveActions

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_ceiling (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  by_cases hp : P.p = 2
  · exact OriginalBinaryAffineArbitraryTopOrdinaryStep.genRank_le_ceiling J block P hp i htop
  · exact OriginalOddAffineArbitraryTopOrdinaryStep.genRank_le_ceiling J block P hp i htop

include P in
theorem exists_generating_finset_of_smaller_subgroups (i : block.Points)
    (hbelow : ∀ (k : ℕ), k < n → ∀ K : Subgroup (Equiv.Perm (Fin k)), 2 ≤ k →
      MulAction.IsPretransitive K (Fin k) →
        ∃ S : Finset K, Subgroup.closure (S : Set K) = ⊤ ∧
          S.card ≤ traceyPermutationGeneratorCeiling k) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling n := by
  letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
  have htop := rank_of_faithful_transitive_action n (of_subgroup_generators n hbelow)
    block.Top block.Points block.degrees_ge_two.2
    (by simpa only [Nat.card_fin] using block.degrees_lt.2)
  have hh := genRank_le_ceiling J block P i htop
  obtain ⟨F,hF,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨F,hgen,hF.le.trans hh⟩

end SymmetricSubgroupAsymptotics.OriginalAffineArbitraryTopOrdinaryStep
