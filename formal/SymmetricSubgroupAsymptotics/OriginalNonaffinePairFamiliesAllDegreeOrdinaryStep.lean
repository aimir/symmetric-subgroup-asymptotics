import SymmetricSubgroupAsymptotics.OriginalNonaffineTinyPairBlockOrdinaryStep
import SymmetricSubgroupAsymptotics.OriginalNonaffineSmallPairFamiliesBlockOrdinaryStep

/-! Original nonaffine imprimitive ordinary induction for EVERY local
degree in the proved pair families. The optional classification corollary
retains exact same-factor model witnesses for the genuinely unpaid branch.
It is not a proof of the global permutation-generator input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffinePairFamiliesAllDegreeOrdinaryStep
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)

/-- Literal unpaid model witness: Tits/sporadic, or a local degree below
1024 in a family for which this consumer does not use a proved pair. -/
def UnpaidModelAtLocalDegree (r : ℕ) (j : CFSG.Index) : Prop :=
  RemainingModel j ∨ (r < 1024 ∧ ¬ PairFamily j)

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (D : NonaffineData block.Component block.Fibre)

/-- No local-degree cutoff and no generating-pair/index callback remains
for alternating, A/B/C/D and Suzuki factors. All data concern the SAME
actual original action and SAME simple factor. -/
theorem genRank_le_ceiling (j : CFSG.Index) (hj : PairFamily j)
    (e : D.Simple ≃* j.Model) (i : block.Points) (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  letI : Finite j.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup j.Model := e.symm.isSimpleGroup
  have hn : ¬ IsMulCommutative j.Model := by
    intro hh
    exact D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr hh)
  rcases CFSGSimpleIndexPacketOrTitsSporadic.model_packet_or_remaining j hn with hpacket | hremaining
  · exact OriginalNonaffineTinyPairBlockOrdinaryStep.genRank_le_ceiling_of_model
      J block D e (OriginalNonaffineSmallPairFamiliesBlockOrdinaryStep.model_pair_of_family j hj)
      hpacket i hbelow
  · have hnot : ¬ RemainingModel j := by
      cases j <;> simp_all only [PairFamily,RemainingModel,not_false_eq_true]
    exact (hnot hremaining).elim

theorem exists_generating_finset (j : CFSG.Index) (hj : PairFamily j)
    (e : D.Simple ≃* j.Model) (i : block.Points) (hbelow : SmallerTransitiveRankBound n) :
    ∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧
      F.card ≤ traceyPermutationGeneratorCeiling n := by
  obtain ⟨F,hF,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨F,hgen,hF.le.trans (genRank_le_ceiling J block D j hj e i hbelow)⟩

/-- The whole original nonaffine block branch now reduces to an actual
unpaid factor witness. Only strictly smaller TRANSITIVE induction and
classification are assumed; no published ordinary-generator bound is used. -/
theorem genRank_le_ceiling_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (i : block.Points) (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      ∃ j : CFSG.Index, UnpaidModelAtLocalDegree (Nat.card block.Fibre) j ∧
        Nonempty (D.Simple ≃* j.Model) := by
  by_cases hlarge : 1024 ≤ Nat.card block.Fibre
  · rcases OriginalNonaffineLargeFibreOrdinaryStep.genRank_le_ceiling_or_actual_remaining_model
      J block D hCFSG i hlarge hbelow with h | ⟨j,hj,e⟩
    · exact Or.inl h
    · exact Or.inr ⟨j,Or.inl hj,e⟩
  · obtain ⟨j,⟨e⟩⟩ := hCFSG.classify D.Simple
    by_cases hj : PairFamily j
    · exact Or.inl (genRank_le_ceiling J block D j hj e i hbelow)
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

end SymmetricSubgroupAsymptotics.OriginalNonaffinePairFamiliesAllDegreeOrdinaryStep
