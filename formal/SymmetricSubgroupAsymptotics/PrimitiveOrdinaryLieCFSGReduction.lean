import SymmetricSubgroupAsymptotics.PrimitiveOrdinaryUnitaryCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryCompleteOrdinary

/-! Every original primitive alternating/Lie ordinary branch is filled
from actual models and actions. Only literal Tits/sporadic tags remain.
Strictly smaller TRANSITIVE induction is retained for the genuine
multifactor reductions; no global coarse permutation input is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveOrdinaryLieCFSGReduction
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction

theorem genRank_le_ceiling_or_actual_remaining_model
    (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hn : 2 ≤ n)
    (J : Subgroup (Equiv.Perm (Fin n)))
    (hprimitive : MulAction.IsPreprimitive J (Fin n))
    (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      ∃ D : NonaffineData J (Fin n), ∃ j : CFSG.Index,
        RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases PrimitiveOrdinaryUnitaryCFSGReduction.genRank_le_ceiling_or_actual_remaining_model
    hCFSG n hn J hprimitive hbelow with h | ⟨D,j,hj,⟨e⟩⟩
  · exact Or.inl h
  rcases hj with hremaining | ⟨hk,_,hmodel⟩
  · exact Or.inr ⟨D,j,hremaining,⟨e⟩⟩
  cases j <;> try { exact False.elim hmodel }
  case twistedA rank q hr hs =>
    exact Or.inl (by simpa only [Nat.card_fin] using
      PrimitiveSocleUnitaryCompleteOrdinary.genRank_le_ceiling D hk rank q hr hs e)

theorem exists_generating_finset_or_actual_remaining_model
    (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hn : 2 ≤ n)
    (J : Subgroup (Equiv.Perm (Fin n)))
    (hprimitive : MulAction.IsPreprimitive J (Fin n))
    (hbelow : SmallerTransitiveRankBound n) :
    (∃ U : Finset J, Subgroup.closure (U : Set J) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling n) ∨
      ∃ D : NonaffineData J (Fin n), ∃ j : CFSG.Index,
        RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases genRank_le_ceiling_or_actual_remaining_model hCFSG n hn J hprimitive hbelow with h | h
  · obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨U,hgen,hU.le.trans h⟩
  · exact Or.inr h

end SymmetricSubgroupAsymptotics.PrimitiveOrdinaryLieCFSGReduction
