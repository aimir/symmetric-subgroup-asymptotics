import SymmetricSubgroupAsymptotics.OriginalNonaffineOrdinaryBinaryUnitaryFrontier
import SymmetricSubgroupAsymptotics.OriginalNonaffineUnitaryBlockOrdinaryStep

/-! Original nonaffine imprimitive ordinary induction through CFSG:
every alternating/Lie tag is supplied by its actual model and source
construction. Only literal Tits/sporadic tags remain. This is a strictly
smaller TRANSITIVE induction step, not the global Tracey theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineOrdinaryLieCFSGReduction
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (D : NonaffineData block.Component block.Fibre)

theorem genRank_le_ceiling_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (i : block.Points) (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases OriginalNonaffineOrdinaryBinaryUnitaryFrontier.genRank_le_ceiling_or_actual_remaining_model
    J block D hCFSG i hbelow with h | ⟨j,hj,⟨e⟩⟩
  · exact Or.inl h
  rcases hj with hremaining | ⟨_,_,hmodel⟩
  · exact Or.inr ⟨j,hremaining,⟨e⟩⟩
  cases j <;> try { exact False.elim hmodel }
  case twistedA rank q hr hs =>
    exact Or.inl (OriginalNonaffineUnitaryBlockOrdinaryStep.genRank_le_ceiling
      J block D rank q hr hs e i hbelow)

theorem exists_generating_finset_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (i : block.Points) (hbelow : SmallerTransitiveRankBound n) :
    (∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧
      F.card ≤ traceyPermutationGeneratorCeiling n) ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases genRank_le_ceiling_or_actual_remaining_model J block D hCFSG i hbelow with h | h
  · obtain ⟨F,hF,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨F,hgen,hF.le.trans h⟩
  · exact Or.inr h

end SymmetricSubgroupAsymptotics.OriginalNonaffineOrdinaryLieCFSGReduction
