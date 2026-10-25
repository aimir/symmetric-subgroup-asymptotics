import SymmetricSubgroupAsymptotics.OriginalNonaffinePrimeTopTinySharpStep
import SymmetricSubgroupAsymptotics.PrimitiveSocleNonpairDegreeEight

/-! The three genuine tiny nonaffine seams reduce to literal Tits/sporadic
factor witnesses. Every other classified model is paid by a proved pair
and its actual index packet, or excluded by genuine proper-index bounds.
The original action, block, simple factor and published sharp FLOOR remain
literal. This is not a global bounded-sharp or McIver-Neumann theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineTinySharpCFSGReduction
open PrimitiveSocleRawStructure PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open TraceySharpHalfDegreeNumerics

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (D : NonaffineData block.Component block.Fibre)

theorem genRank_le_sharpFloor_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (hshape : (Nat.card block.Fibre = 6 ∧ Nat.card block.Points = 2) ∨
      (Nat.card block.Fibre = 5 ∧ Nat.card block.Points = 3) ∨
      (Nat.card block.Fibre = 7 ∧ Nat.card block.Points = 3)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  have hr : Nat.card block.Fibre ≤ 7 := by rcases hshape with h|h|h <;> omega
  rcases PrimitiveSocleNonpairDegreeEight.pair_family_or_actual_remaining_of_degree_le_seven
    D hCFSG hr with ⟨j,hj,⟨e⟩⟩ | hremaining
  · exact Or.inl (OriginalNonaffinePrimeTopTinySharpStep.genRank_le_sharpFloor_of_pair_family
      J block D j hj e hshape)
  · exact Or.inr hremaining

theorem exists_generating_finset_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (hshape : (Nat.card block.Fibre = 6 ∧ Nat.card block.Points = 2) ∨
      (Nat.card block.Fibre = 5 ∧ Nat.card block.Points = 3) ∨
      (Nat.card block.Fibre = 7 ∧ Nat.card block.Points = 3)) :
    (∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧ F.card ≤ sharpFloor n) ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases genRank_le_sharpFloor_or_actual_remaining_model J block D hCFSG hshape with hg | hr
  · obtain ⟨F,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨F,hgen,hcard.le.trans hg⟩
  · exact Or.inr hr

/-- The weaker half-degree consequence is a separate corollary of the
literal sharp result; the two targets are never identified. -/
theorem genRank_le_half_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (hshape : (Nat.card block.Fibre = 6 ∧ Nat.card block.Points = 2) ∨
      (Nat.card block.Fibre = 5 ∧ Nat.card block.Points = 3) ∨
      (Nat.card block.Fibre = 7 ∧ Nat.card block.Points = 3)) :
    MarkedC4.genRank J ≤ n/2 ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases genRank_le_sharpFloor_or_actual_remaining_model J block D hCFSG hshape with hg | hr
  · have hproduct : Nat.card block.Fibre * Nat.card block.Points = n := by
      simpa only [Nat.card_fin] using block.degree_product
    have hn : 4 ≤ n := by
      rcases hshape with ⟨hr,ht⟩ | ⟨hr,ht⟩ | ⟨hr,ht⟩ <;>
        rw [hr,ht] at hproduct <;> omega
    exact Or.inl (hg.trans (TraceySharpHalfDegreeNumerics.sharpFloor_le_half n hn))
  · exact Or.inr hr

end SymmetricSubgroupAsymptotics.OriginalNonaffineTinySharpCFSGReduction
