import SymmetricSubgroupAsymptotics.ElementarySylowEightActualTopObstructionFalse

/-! Remove only the SAME original elementary-Sylow top obstruction from
the strongest existing affine-block sharp reduction. The independent
cumulative global failed-half witness of degree≤10 is retained exactly. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpActualTopComplete
open TraceySharpHalfDegreeNumerics

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_sharpFloor_or_cumulative_global
    (hCFSG : CFSG.CFSGClassification) (hsmall : n<22) :
    MarkedC4.genRank J≤ sharpFloor n ∨
      Nonempty (OriginalAffineBoundedSharpCoTwoTopRefinement.CumulativeGlobalCounterexample 10) := by
  rcases OriginalAffineBoundedSharpCoTwoTopRefinement.genRank_le_sharpFloor_or_cumulative_sporadic_obstructions
    J block P hCFSG hsmall with hpaid | htop | hglobal
  · exact Or.inl hpaid
  · exact (ElementarySylowEightActualTopObstructionFalse.no_cumulative_actual_top_obstruction htop.2).elim
  · exact Or.inr hglobal

include P in
theorem exists_generating_finset_or_cumulative_global
    (hCFSG : CFSG.CFSGClassification) (hsmall : n<22) :
    (∃ U : Finset J, Subgroup.closure (U : Set J)=⊤ ∧ U.card≤ sharpFloor n) ∨
      Nonempty (OriginalAffineBoundedSharpCoTwoTopRefinement.CumulativeGlobalCounterexample 10) := by
  rcases genRank_le_sharpFloor_or_cumulative_global J block P hCFSG hsmall with hpaid | hglobal
  · obtain ⟨U,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨U,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr hglobal

end SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpActualTopComplete
