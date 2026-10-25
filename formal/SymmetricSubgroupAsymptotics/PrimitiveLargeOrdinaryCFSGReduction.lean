import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof
import SymmetricSubgroupAsymptotics.PrimitiveAffineCoarseOrdinaryComplete
import SymmetricSubgroupAsymptotics.PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexPacketOrTitsSporadic
import SymmetricSubgroupAsymptotics.PrimitiveSocleMultipleFactorOrdinaryTail

/-! The whole actual large primitive ordinary-generator branch.
The proved raw socle dichotomy, complete affine branch, all proved
one-factor family consumers, and genuine multi-factor strictly-smaller
TRANSITIVE induction are combined on the original permutation subgroup.
Only actual Tits/sporadic simple-model witnesses remain. This is not a
global coarse theorem: no same-degree permutation bound is assumed or
deduced for arbitrary imprimitive actions. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveLargeOrdinaryCFSGReduction
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction

theorem genRank_le_ceiling_or_actual_remaining_model
    (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hn : 1024 ≤ n)
    (J : Subgroup (Equiv.Perm (Fin n)))
    (hprimitive : MulAction.IsPreprimitive J (Fin n))
    (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      ∃ D : NonaffineData J (Fin n), ∃ i : CFSG.Index,
        RemainingModel i ∧ Nonempty (D.Simple ≃* i.Model) := by
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1 < n by omega))
  letI : MulAction.IsPreprimitive J (Fin n) := hprimitive
  obtain ⟨P⟩ := publishedONanScottStructure J (Fin n)
  cases P with
  | inr P =>
    exact Or.inl (PrimitiveAffineCoarseOrdinaryComplete.genRank_le_ceiling
      n (by omega) J P hprimitive)
  | inl D =>
    by_cases hk : D.factorCount = 1
    · rcases PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction.genRank_le_ceiling_or_actual_remaining_model
          D hCFSG hk (by simpa only [Nat.card_fin] using hn) with hb | ⟨i, hi, he⟩
      · exact Or.inl (by simpa only [Nat.card_fin] using hb)
      · exact Or.inr ⟨D, i, hi, he⟩
    · have hk2 : 2 ≤ D.factorCount := by have := D.factorCount_pos; omega
      rcases CFSGSimpleIndexPacketOrTitsSporadic.factor_packet_or_actual_remaining_model
          D hCFSG with hb | ⟨i, hi, he⟩
      · obtain ⟨ell, hell⟩ := exists_leastProperIndex D.Simple
        obtain ⟨horder, houter⟩ := hb ell hell
        have h := PrimitiveSocleMultipleFactorOrdinaryTail.genRank_le_ceiling
          D ell (by simpa only [Nat.card_fin] using hbelow) hell hk2 horder
          (by simpa only [Nat.card_fin] using hn) houter
        exact Or.inl (by simpa only [Nat.card_fin] using h)
      · exact Or.inr ⟨D, i, hi, he⟩

theorem exists_generating_finset_or_actual_remaining_model
    (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hn : 1024 ≤ n)
    (J : Subgroup (Equiv.Perm (Fin n)))
    (hprimitive : MulAction.IsPreprimitive J (Fin n))
    (hbelow : SmallerTransitiveRankBound n) :
    (∃ U : Finset J, Subgroup.closure (U : Set J) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling n) ∨
      ∃ D : NonaffineData J (Fin n), ∃ i : CFSG.Index,
        RemainingModel i ∧ Nonempty (D.Simple ≃* i.Model) := by
  rcases genRank_le_ceiling_or_actual_remaining_model hCFSG n hn J hprimitive hbelow with h | h
  · obtain ⟨U, hU, hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨U, hgen, hU.le.trans h⟩
  · exact Or.inr h

end SymmetricSubgroupAsymptotics.PrimitiveLargeOrdinaryCFSGReduction
