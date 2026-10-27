import SymmetricSubgroupAsymptotics.BoundedSharpEightClosedActualResidual
import SymmetricSubgroupAsymptotics.TenPointGlobalCounterexampleCompleteCFSG

/-! Preserve the strongest original primitive/block sporadic witnesses
while eliminating the independent global10 failure by its proved theorem.
All previous actual affine8/16 and Tits closures remain inherited. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BoundedSharpTenClosedActualResidual
open TraceySharpHalfDegreeNumerics
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

def ActualResidual : Prop :=
  BoundedSharpTitsCompleteActualResidual.PrimitiveSporadicResidual J ∨
    BoundedSharpTitsCompleteActualResidual.OriginalNonaffineSporadicResidual J

 theorem genRank_le_sharpFloor_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (hlo : 4≤n) (hhi : n≤21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases BoundedSharpEightClosedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hCFSG hlo hhi ht with hpaid | hbad
  · exact Or.inl hpaid
  · rcases hbad with hprimitive | hglobal | hnonaffine
    · exact Or.inr (Or.inl hprimitive)
    · exact (TenPointGlobalCounterexampleCompleteCFSG.no_cumulative_global_counterexample_ten
        hCFSG hglobal).elim
    · exact Or.inr (Or.inr hnonaffine)

 theorem exists_generating_finset_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (hlo : 4≤n) (hhi : n≤21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    (∃ U : Finset J,Subgroup.closure (U : Set J)=⊤ ∧ U.card ≤ sharpFloor n) ∨ ActualResidual J := by
  rcases genRank_le_sharpFloor_or_actual_residual J hCFSG hlo hhi ht with hpaid | hbad
  · obtain ⟨U,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨U,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr hbad

end SymmetricSubgroupAsymptotics.BoundedSharpTenClosedActualResidual
