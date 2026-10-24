import SymmetricSubgroupAsymptotics.ActualWreathSixOrderCoarseOrdinaryStep
import SymmetricSubgroupAsymptotics.OriginalBlockOrdinaryCompressionState
import SymmetricSubgroupAsymptotics.TraceyStrictlySmallerTransitiveActions

/-! A genuine original three-point fibre gives a local subgroup ofS3,
so its order divides6. The independent correlated order-six recurrence
then gives the original coarse bound using only the strictly-smaller
TRANSITIVE top IH. No affine recognition or global MN/Tracey is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalTernaryCoarseOrdinaryStep
open TraceyStrictlySmallerTransitiveActions

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

theorem component_card_dvd_six (hr : Nat.card block.Fibre = 3) :
    Nat.card block.Component ∣ 6 := by
  classical
  letI : Fintype block.Fibre := Fintype.ofFinite _
  have hd := Subgroup.card_dvd_of_injective block.Component.subtype block.Component.subtype_injective
  have hperm : Nat.card (Equiv.Perm block.Fibre) = 6 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_eq_nat_card,hr]
    norm_num
  simpa only [hperm] using hd

theorem genRank_le_ceiling (hr : Nat.card block.Fibre = 3) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have horder : Nat.card (OriginalBlockOrdinaryCompressionState.initialState J block).D ∣ 6 :=
    component_card_dvd_six J block hr
  have htop' : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Fintype.card block.Points) := by
    simpa only [Fintype.card_eq_nat_card] using htop
  have hh := ActualWreathSixOrderCoarseOrdinaryStep.genRank_le_ceiling
    (OriginalBlockOrdinaryCompressionState.initialState J block) i hI horder htop'
  change MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling (3*Fintype.card block.Points) at hh
  have hn : n = 3*Fintype.card block.Points := by
    simpa only [hr,Nat.card_fin,Fintype.card_eq_nat_card] using block.degree_product.symm
  simpa only [← hn] using hh

theorem exists_generating_finset_of_smaller_subgroups (hr : Nat.card block.Fibre = 3)
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
  have hh := genRank_le_ceiling J block hr i htop
  obtain ⟨F,hF,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨F,hgen,hF.le.trans hh⟩

end SymmetricSubgroupAsymptotics.OriginalTernaryCoarseOrdinaryStep
