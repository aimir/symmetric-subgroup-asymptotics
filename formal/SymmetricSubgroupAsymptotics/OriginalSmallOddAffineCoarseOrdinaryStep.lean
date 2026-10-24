import SymmetricSubgroupAsymptotics.ActualWreathSmallAffineCoarseOrdinaryStep
import SymmetricSubgroupAsymptotics.PrimitiveAffineSmallLocalOrderDivisibility
import SymmetricSubgroupAsymptotics.OriginalBlockOrdinaryCompressionState
import SymmetricSubgroupAsymptotics.TraceyStrictlySmallerTransitiveActions

/-! The literal primitive affine components of degrees5,7,9 supply
orders dividing20,42,432 through their actual translation charts. The
same correlated original block state then satisfies the coarse bound
from its strictly-smaller TRANSITIVE top IH, with no global input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalSmallOddAffineCoarseOrdinaryStep
open TraceyStrictlySmallerTransitiveActions

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem component_card_dvd_orderBound
    (hr : Nat.card block.Fibre = 5 ∨ Nat.card block.Fibre = 7 ∨ Nat.card block.Fibre = 9) :
    Nat.card block.Component ∣
      ActualWreathSmallAffineCoarseOrdinaryStep.orderBound (Nat.card block.Fibre) := by
  let x : block.Fibre := ⟨x₀,block.map_base⟩
  rcases hr with hr | hr | hr
  · rw [hr]
    simpa [ActualWreathSmallAffineCoarseOrdinaryStep.orderBound] using
      PrimitiveAffineSmallLocalOrderDivisibility.card_dvd_twenty P x hr
  · rw [hr]
    simpa [ActualWreathSmallAffineCoarseOrdinaryStep.orderBound] using
      PrimitiveAffineSmallLocalOrderDivisibility.card_dvd_forty_two P x hr
  · rw [hr]
    simpa [ActualWreathSmallAffineCoarseOrdinaryStep.orderBound] using
      PrimitiveAffineSmallLocalOrderDivisibility.card_dvd_four_hundred_thirty_two
        P block.component_preprimitive x hr

include P in
theorem genRank_le_ceiling
    (hr : Nat.card block.Fibre = 5 ∨ Nat.card block.Fibre = 7 ∨ Nat.card block.Fibre = 9)
    (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have horder : Nat.card (OriginalBlockOrdinaryCompressionState.initialState J block).D ∣
      ActualWreathSmallAffineCoarseOrdinaryStep.orderBound (Nat.card block.Fibre) :=
    component_card_dvd_orderBound J block P hr
  have htop' : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Fintype.card block.Points) := by
    simpa only [Fintype.card_eq_nat_card] using htop
  have hh := ActualWreathSmallAffineCoarseOrdinaryStep.genRank_le_ceiling
    (OriginalBlockOrdinaryCompressionState.initialState J block) i hI
      (Nat.card block.Fibre) hr horder htop'
  change MarkedC4.genRank J ≤
    traceyPermutationGeneratorCeiling (Nat.card block.Fibre*Fintype.card block.Points) at hh
  have hn : n = Nat.card block.Fibre*Fintype.card block.Points := by
    simpa only [Nat.card_fin,Fintype.card_eq_nat_card] using block.degree_product.symm
  simpa only [← hn] using hh

include P in
theorem exists_generating_finset_of_smaller_subgroups
    (hr : Nat.card block.Fibre = 5 ∨ Nat.card block.Fibre = 7 ∨ Nat.card block.Fibre = 9)
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
  have hh := genRank_le_ceiling J block P hr i htop
  obtain ⟨F,hF,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨F,hgen,hF.le.trans hh⟩

end SymmetricSubgroupAsymptotics.OriginalSmallOddAffineCoarseOrdinaryStep
