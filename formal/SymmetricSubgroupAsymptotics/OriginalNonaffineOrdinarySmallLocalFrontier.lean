import SymmetricSubgroupAsymptotics.OriginalNonaffineThirtyTwoOrdinaryStep
import SymmetricSubgroupAsymptotics.OriginalNonaffinePairFamiliesAllDegreeOrdinaryStep

/-! Whole original nonaffine imprimitive ordinary reduction. Every local
size>=32 is handled by actual strict-coset induction, and the proved pair
families are handled at every smaller local size. The residual is an
explicit SAME-factor model witness, not a hidden generator callback.
This theorem does not discharge the global coarse permutation input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineOrdinarySmallLocalFrontier
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)

/-- The exact unpaid local-model frontier; the actual factor equivalence
in the theorem below rules out any commutative model tag automatically. -/
def UnpaidModelAtLocalDegree (r : ℕ) (j : CFSG.Index) : Prop :=
  RemainingModel j ∨ (r < 32 ∧ ¬ PairFamily j)

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (D : NonaffineData block.Component block.Fibre)

theorem genRank_le_ceiling_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (i : block.Points) (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      ∃ j : CFSG.Index, UnpaidModelAtLocalDegree (Nat.card block.Fibre) j ∧
        Nonempty (D.Simple ≃* j.Model) := by
  by_cases hlarge : 32 ≤ Nat.card block.Fibre
  · rcases OriginalNonaffineThirtyTwoOrdinaryStep.genRank_le_ceiling_or_actual_remaining_model
      J block D hCFSG i hlarge hbelow with h | ⟨j,hj,e⟩
    · exact Or.inl h
    · exact Or.inr ⟨j,Or.inl hj,e⟩
  · obtain ⟨j,⟨e⟩⟩ := hCFSG.classify D.Simple
    by_cases hj : PairFamily j
    · exact Or.inl (OriginalNonaffinePairFamiliesAllDegreeOrdinaryStep.genRank_le_ceiling
        J block D j hj e i hbelow)
    · exact Or.inr ⟨j,Or.inr ⟨by omega,hj⟩,⟨e⟩⟩

theorem exists_generating_finset_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (i : block.Points) (hbelow : SmallerTransitiveRankBound n) :
    (∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧
      F.card ≤ traceyPermutationGeneratorCeiling n) ∨
      ∃ j : CFSG.Index, UnpaidModelAtLocalDegree (Nat.card block.Fibre) j ∧
        Nonempty (D.Simple ≃* j.Model) := by
  rcases genRank_le_ceiling_or_actual_remaining_model J block D hCFSG i hbelow with h | h
  · obtain ⟨F,hF,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨F,hgen,hF.le.trans h⟩
  · exact Or.inr h

end SymmetricSubgroupAsymptotics.OriginalNonaffineOrdinarySmallLocalFrontier
