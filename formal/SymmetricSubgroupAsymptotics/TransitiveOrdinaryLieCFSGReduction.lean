import SymmetricSubgroupAsymptotics.PrimitiveOrdinaryLieCFSGReduction
import SymmetricSubgroupAsymptotics.OriginalAffineArbitraryTopOrdinaryStep
import SymmetricSubgroupAsymptotics.OriginalNonaffineOrdinaryLieCFSGReduction

/-! The actual all-transitive ordinary degree-induction step. The SAME
original action is primitive, or its actual minimal block has a primitive
affine/nonaffine component. Every alternating/Lie branch is supplied by
proved sources. A failure retains literal Tits/sporadic data on the
original primitive action or actual original block component. No global
Tracey input or finite-model generator callback is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TransitiveOrdinaryLieCFSGReduction
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)]

def PrimitiveFiniteModelResidual : Prop :=
  MulAction.IsPreprimitive J (Fin n) ∧
    ∃ D : NonaffineData J (Fin n), ∃ j : CFSG.Index,
      RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model)

def BlockFiniteModelResidual : Prop :=
  ¬ MulAction.IsPreprimitive J (Fin n) ∧
    ∃ x₀ : Fin n, ∃ block : OriginalMinimalBlock (A := J) x₀,
      ∃ D : NonaffineData block.Component block.Fibre, ∃ j : CFSG.Index,
        RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model)

def ActualFiniteModelResidual : Prop :=
  PrimitiveFiniteModelResidual J ∨ BlockFiniteModelResidual J

theorem genRank_le_ceiling_or_actual_finite_model
    (hCFSG : CFSG.CFSGClassification) (hn : 2 ≤ n)
    (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      ActualFiniteModelResidual J := by
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1 < n by omega))
  by_cases hp : MulAction.IsPreprimitive J (Fin n)
  · rcases PrimitiveOrdinaryLieCFSGReduction.genRank_le_ceiling_or_actual_remaining_model
      hCFSG n hn J hp hbelow with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hp,h⟩)
  · let x₀ : Fin n := ⟨0,by omega⟩
    obtain ⟨block⟩ := originalMinimalBlock_nonempty (A := J) x₀ hp
    letI : Fintype block.Points := Fintype.ofFinite _
    letI : Nontrivial block.Fibre := Finite.one_lt_card_iff_nontrivial.mp
      (by have h := block.degrees_ge_two.1; omega)
    letI : MulAction.IsPreprimitive block.Component block.Fibre := block.component_preprimitive
    obtain ⟨P⟩ := publishedONanScottStructure block.Component block.Fibre
    cases P with
    | inr P =>
      letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
      have htop := rank_of_faithful_transitive_action n hbelow block.Top block.Points
        block.degrees_ge_two.2 (by simpa only [Nat.card_fin] using block.degrees_lt.2)
      exact Or.inl (OriginalAffineArbitraryTopOrdinaryStep.genRank_le_ceiling
        J block P block.base htop)
    | inl D =>
      rcases OriginalNonaffineOrdinaryLieCFSGReduction.genRank_le_ceiling_or_actual_remaining_model
        J block D hCFSG block.base hbelow with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨hp,x₀,block,D,h⟩)

theorem exists_generating_finset_or_actual_finite_model
    (hCFSG : CFSG.CFSGClassification) (hn : 2 ≤ n)
    (hbelow : SmallerTransitiveRankBound n) :
    (∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling n) ∨ ActualFiniteModelResidual J := by
  rcases genRank_le_ceiling_or_actual_finite_model J hCFSG hn hbelow with h | h
  · obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨S,hgen,hS.le.trans h⟩
  · exact Or.inr h

end SymmetricSubgroupAsymptotics.TransitiveOrdinaryLieCFSGReduction
