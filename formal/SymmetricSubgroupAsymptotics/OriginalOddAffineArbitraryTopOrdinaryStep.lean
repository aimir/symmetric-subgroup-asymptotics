import SymmetricSubgroupAsymptotics.OriginalOddAffineLargeLocalOrdinaryStep
import SymmetricSubgroupAsymptotics.OriginalSmallOddAffineCoarseOrdinaryStep
import SymmetricSubgroupAsymptotics.OriginalTernaryCoarseOrdinaryStep

/-! Every actual odd-characteristic affine minimal-block component is
paid, over an arbitrary genuine top action. The sole quantitative IH is
on that strictly-smaller TRANSITIVE action. This closes the odd-affine
imprimitive induction branch, not the global permutation theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalOddAffineArbitraryTopOrdinaryStep
open OriginalAffineBlockCharacteristicHead TraceyStrictlySmallerTransitiveActions

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_ceiling (hp : P.p ≠ 2) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  by_cases h11 : 11 ≤ Nat.card block.Fibre
  · exact OriginalOddAffineLargeLocalOrdinaryStep.genRank_le_ceiling J block P hp h11 i htop
  have hoddPower : Odd (P.p^translationDimension J block P) :=
    (P.p_prime.odd_of_ne_two hp).pow
  have hodd : Odd (Nat.card block.Fibre) :=
    (fibre_card_eq_prime_pow_dimension J block P).symm ▸ hoddPower
  have hmod := Nat.odd_iff.mp hodd
  have hmin := block.degrees_ge_two.1
  have hsmall : Nat.card block.Fibre = 3 ∨ Nat.card block.Fibre = 5 ∨
      Nat.card block.Fibre = 7 ∨ Nat.card block.Fibre = 9 := by omega
  rcases hsmall with h3 | h5 | h7 | h9
  · exact OriginalTernaryCoarseOrdinaryStep.genRank_le_ceiling J block h3 i htop
  · exact OriginalSmallOddAffineCoarseOrdinaryStep.genRank_le_ceiling J block P (Or.inl h5) i htop
  · exact OriginalSmallOddAffineCoarseOrdinaryStep.genRank_le_ceiling J block P
      (Or.inr (Or.inl h7)) i htop
  · exact OriginalSmallOddAffineCoarseOrdinaryStep.genRank_le_ceiling J block P
      (Or.inr (Or.inr h9)) i htop

theorem exists_generating_finset_of_smaller_subgroups (hp : P.p ≠ 2)
    (i : block.Points)
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
  have hh := genRank_le_ceiling J block P hp i htop
  obtain ⟨F,hF,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨F,hgen,hF.le.trans hh⟩

end SymmetricSubgroupAsymptotics.OriginalOddAffineArbitraryTopOrdinaryStep
