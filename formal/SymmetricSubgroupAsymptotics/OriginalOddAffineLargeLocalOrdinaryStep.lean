import SymmetricSubgroupAsymptotics.OriginalOddAffineTameOrderTail
import SymmetricSubgroupAsymptotics.OriginalAffineSharpSmallSeeds
import SymmetricSubgroupAsymptotics.OddPrimePowerSmallDimensionBands

/-! Independent odd-affine coarse induction in every local degree at
least11. The finite prime-power band lemma and original dimension/order
bounds discharge every scalar premise. The smaller transitive top action
is retained literally. Local degrees3,5,7,9 are not claimed here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalOddAffineLargeLocalOrdinaryStep
open OriginalAffineBlockCharacteristicHead TraceyStrictlySmallerTransitiveActions

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_ceiling (hp : P.p ≠ 2) (hr : 11 ≤ Nat.card block.Fibre)
    (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  by_cases h128 : 128 ≤ Nat.card block.Fibre
  · exact OriginalOddAffineTameOrderTail.genRank_le_ceiling_of_local_degree_ge_128
      J block P hp h128 i htop
  have hband := OddPrimePowerSmallDimensionBands.bands P.p (translationDimension J block P)
    (Nat.card block.Fibre) P.p_prime hp (fibre_card_eq_prime_pow_dimension J block P)
      hr (by omega)
  rcases hband with hd1 | ⟨hd2,h25⟩ | ⟨hp3,hd3⟩ | ⟨hd4,h64⟩
  · exact OriginalAffineSharpSmallSeeds.genRank_le_of_dimension_one J block P hd1 hr i htop
  · by_cases h32 : 32 ≤ Nat.card block.Fibre
    · exact OriginalAffineSharpDyadicBands.genRank_le_of_dimension_two J block P hd2 h32 i htop
    · exact OriginalAffineSharpSmallSeeds.genRank_le_of_dimension_two_interval
        J block P hd2 h25 (by omega) i htop
  · exact OriginalAffineSharpSmallSeeds.genRank_le_of_ternary_cubic J block P hp3 hd3 i htop
  · exact OriginalAffineSharpDyadicBands.genRank_le_of_dimension_four J block P hd4 h64 i htop

theorem exists_generating_finset_of_smaller_subgroups (hp : P.p ≠ 2)
    (hr : 11 ≤ Nat.card block.Fibre) (i : block.Points)
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
  have hh := genRank_le_ceiling J block P hp hr i htop
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨S,hgen,hS.le.trans hh⟩

end SymmetricSubgroupAsymptotics.OriginalOddAffineLargeLocalOrdinaryStep
