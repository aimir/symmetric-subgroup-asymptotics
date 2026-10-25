import SymmetricSubgroupAsymptotics.PrimitiveLargeOrdinaryCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveMultifactorOrdinaryCFSGReduction

/-! Original primitive ordinary induction at every degree. The entire
affine and multifactor branches, all proved pair families, and every
large one-factor branch are filled internally. Only a literal finite
model or a bounded non-pair one-factor action remains. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveOrdinaryBoundedOneFactorCFSGReduction
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)

def RemainingAtDegree (n k : ℕ) (j : CFSG.Index) : Prop :=
  RemainingModel j ∨ (k=1 ∧ n<1024 ∧ ¬ PairFamily j)

theorem genRank_le_ceiling_or_actual_remaining_model
    (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hn : 2≤n)
    (J : Subgroup (Equiv.Perm (Fin n)))
    (hprimitive : MulAction.IsPreprimitive J (Fin n))
    (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      ∃ D : NonaffineData J (Fin n), ∃ j : CFSG.Index,
        RemainingAtDegree n D.factorCount j ∧ Nonempty (D.Simple≃*j.Model) := by
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1<n by omega))
  letI : MulAction.IsPreprimitive J (Fin n) := hprimitive
  obtain ⟨P⟩ := publishedONanScottStructure J (Fin n)
  cases P with
  | inr P =>
    exact Or.inl (PrimitiveAffineCoarseOrdinaryComplete.genRank_le_ceiling n hn J P hprimitive)
  | inl D =>
    by_cases hk : D.factorCount=1
    · by_cases hlarge : 1024≤n
      · rcases PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction.genRank_le_ceiling_or_actual_remaining_model
          D hCFSG hk (by simpa only [Nat.card_fin] using hlarge) with h | ⟨j,hj,e⟩
        · exact Or.inl (by simpa only [Nat.card_fin] using h)
        · exact Or.inr ⟨D,j,Or.inl hj,e⟩
      · obtain ⟨j,⟨e⟩⟩ := hCFSG.classify D.Simple
        by_cases hj : PairFamily j
        · exact Or.inl (by simpa only [Nat.card_fin] using
            (PrimitiveSoclePairFamiliesCompleteOrdinary.genRank_le_ceiling D j hj e
              (by simpa only [Nat.card_fin] using hbelow)))
        · exact Or.inr ⟨D,j,Or.inr ⟨hk,by omega,hj⟩,⟨e⟩⟩
    · rcases PrimitiveMultifactorOrdinaryCFSGReduction.genRank_le_ceiling_or_actual_remaining_model
          D hCFSG (by have hp := D.factorCount_pos; omega)
          (by simpa only [Nat.card_fin] using hbelow) with h | ⟨j,hj,e⟩
      · exact Or.inl (by simpa only [Nat.card_fin] using h)
      · exact Or.inr ⟨D,j,Or.inl hj,e⟩

theorem exists_generating_finset_or_actual_remaining_model
    (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hn : 2≤n)
    (J : Subgroup (Equiv.Perm (Fin n)))
    (hprimitive : MulAction.IsPreprimitive J (Fin n))
    (hbelow : SmallerTransitiveRankBound n) :
    (∃ S : Finset J, Subgroup.closure (S : Set J)=⊤ ∧
      S.card≤traceyPermutationGeneratorCeiling n) ∨
      ∃ D : NonaffineData J (Fin n), ∃ j : CFSG.Index,
        RemainingAtDegree n D.factorCount j ∧ Nonempty (D.Simple≃*j.Model) := by
  rcases genRank_le_ceiling_or_actual_remaining_model hCFSG n hn J hprimitive hbelow with h | h
  · obtain ⟨S,hcard,hS⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨S,hS,hcard.le.trans h⟩
  · exact Or.inr h

end SymmetricSubgroupAsymptotics.PrimitiveOrdinaryBoundedOneFactorCFSGReduction
