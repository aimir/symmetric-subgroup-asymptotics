import SymmetricSubgroupAsymptotics.BoundedSharpTitsCompleteActualResidual
import SymmetricSubgroupAsymptotics.EightPointHalfDegreeCompleteCFSG
import SymmetricSubgroupAsymptotics.ElementarySylowEightActualTopObstructionFalse

/-! Cumulative bounded sharp reduction after both eight-point closures.
The original primitive sporadic D, independent global ten-point failure,
and original nonaffine block D remain exactly those of the old wrapper.
No replacement estimate, callback or weaker tag guard is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BoundedSharpEightClosedActualResidual
open TraceySharpHalfDegreeNumerics

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

def ActualResidual : Prop :=
  BoundedSharpTitsCompleteActualResidual.PrimitiveSporadicResidual J ∨
    Nonempty (OriginalAffineBoundedSharpCoTwoTopRefinement.CumulativeGlobalCounterexample 10) ∨
      BoundedSharpTitsCompleteActualResidual.OriginalNonaffineSporadicResidual J

theorem not_primitive_affine_residual (hCFSG : CFSG.CFSGClassification) :
    ¬BoundedSharpTitsCompleteActualResidual.PrimitiveAffineResidual J := by
  rintro ⟨h16,hp,hprofile,hbad⟩
  exact EightPointHalfDegreeCompleteCFSG.no_cumulative_global_counterexample_eight hCFSG hbad

theorem not_original_affine_top_residual :
    ¬BoundedSharpTitsCompleteActualResidual.OriginalAffineTopResidual J := by
  rintro ⟨h16,ht,hrest⟩
  letI : MulAction.IsPretransitive J (Fin n) := ht
  obtain ⟨x₀,block,hprofile,hbad⟩ := hrest
  exact ElementarySylowEightActualTopObstructionFalse.no_cumulative_actual_top_obstruction hbad

theorem genRank_le_sharpFloor_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (hlo : 4≤n) (hhi : n≤21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J≤ sharpFloor n ∨ ActualResidual J := by
  rcases BoundedSharpTitsCompleteActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hCFSG hlo hhi ht with hpaid | hbad
  · exact Or.inl hpaid
  · rcases hbad with haffine | hprimitive | htop | hglobal | hnonaffine
    · exact (not_primitive_affine_residual J hCFSG haffine).elim
    · exact Or.inr (Or.inl hprimitive)
    · exact (not_original_affine_top_residual J htop).elim
    · exact Or.inr (Or.inr (Or.inl hglobal))
    · exact Or.inr (Or.inr (Or.inr hnonaffine))

theorem exists_generating_finset_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (hlo : 4≤n) (hhi : n≤21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    (∃ U : Finset J, Subgroup.closure (U : Set J)=⊤ ∧ U.card≤ sharpFloor n) ∨ ActualResidual J := by
  rcases genRank_le_sharpFloor_or_actual_residual J hCFSG hlo hhi ht with hpaid | hbad
  · obtain ⟨U,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨U,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr hbad

end SymmetricSubgroupAsymptotics.BoundedSharpEightClosedActualResidual
