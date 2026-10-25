import SymmetricSubgroupAsymptotics.OriginalNonaffineOrdinaryUnitarySmallLocalFrontier
import SymmetricSubgroupAsymptotics.OriginalNonaffineSmallUnitaryBlockOrdinaryStep

/-! All original nonaffine block tags are supplied except literal
Tits/sporadic tags and the precise binary rank-three unitary factor at
actual local8..31. This reduction keeps the SAME model equivalence and
original degree, and makes no global coarse permutation claim. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineOrdinaryBinaryUnitaryFrontier
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction

def UnpaidModelAtLocalDegree (r : ℕ) (j : CFSG.Index) : Prop :=
  RemainingModel j ∨ (8 ≤ r ∧ r < 32 ∧ match j with
    | .twistedA rank q _ _ => rank = 3 ∧ q.order = 2
    | _ => False)

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (D : NonaffineData block.Component block.Fibre)

theorem genRank_le_ceiling_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (i : block.Points) (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      ∃ j : CFSG.Index, UnpaidModelAtLocalDegree (Nat.card block.Fibre) j ∧
        Nonempty (D.Simple ≃* j.Model) := by
  rcases OriginalNonaffineOrdinaryUnitarySmallLocalFrontier.genRank_le_ceiling_or_actual_remaining_model
    J block D hCFSG i hbelow with h | ⟨j,hj,⟨e⟩⟩
  · exact Or.inl h
  rcases hj with hremaining | ⟨hsmall,hmin⟩
  · exact Or.inr ⟨j,Or.inl hremaining,⟨e⟩⟩
  cases j <;> try { exact False.elim hmin }
  case twistedA rank q hr hs =>
    rcases OriginalNonaffineSmallUnitaryBlockOrdinaryStep.genRank_le_ceiling_or_binary_rank_three
      J block D rank q hr hs e i hbelow with h | ⟨hr3,hq2,_⟩
    · exact Or.inl h
    · have hr8 : 8 ≤ Nat.card block.Fibre := by
        norm_num [hr3,hq2] at hmin
        simpa only [Fintype.card_eq_nat_card] using hmin
      exact Or.inr ⟨.twistedA rank q hr hs,Or.inr ⟨hr8,hsmall,hr3,hq2⟩,⟨e⟩⟩

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

end SymmetricSubgroupAsymptotics.OriginalNonaffineOrdinaryBinaryUnitaryFrontier
