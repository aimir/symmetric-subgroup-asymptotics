import SymmetricSubgroupAsymptotics.BoundedSharpTenClosedActualResidual
import SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionSmallActionExclusion

/-! Preserve the strongest ten-closed original bounded-sharp witnesses,
adding proved exclusion of all four actual Y tags in primitive degree≤21
and original component degree≤10. Existing global-exclusion guards are
retained on the SAME simple group and block. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BoundedSharpTenClosedYExcludedActualResidual
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open OriginalAffineBoundedSharpCoTwoTopRefinement
open PrimitiveSocleYSectionOrdinaryTail
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

def PrimitiveSporadicResidual : Prop :=
  MulAction.IsPreprimitive J (Fin n) ∧
    ∃ D : NonaffineData J (Fin n), ∃ s : CFSG.Sporadic,
      Nonempty (D.Simple ≃* (CFSG.Index.sporadic s).Model) ∧
        (n≤10 → ¬GlobalExcluded s) ∧ ¬IsYSectionModel s

def OriginalNonaffineSporadicResidual : Prop :=
  ∃ ht : MulAction.IsPretransitive J (Fin n),
    letI := ht
    ∃ x₀ : Fin n, ∃ block : OriginalMinimalBlock (A := J) x₀,
      Nat.card block.Fibre≤10 ∧
        ∃ D : NonaffineData block.Component block.Fibre, ∃ s : CFSG.Sporadic,
          Nonempty (D.Simple ≃* (CFSG.Index.sporadic s).Model) ∧
            ¬GlobalExcluded s ∧ ¬IsYSectionModel s

def ActualResidual : Prop := PrimitiveSporadicResidual J ∨ OriginalNonaffineSporadicResidual J

theorem refine_primitive (hhi : n≤21)
    (h : BoundedSharpTitsCompleteActualResidual.PrimitiveSporadicResidual J) :
    PrimitiveSporadicResidual J := by
  obtain ⟨hp,D,s,⟨e⟩,hglobal⟩ := h
  refine ⟨hp,D,s,⟨e⟩,hglobal,?_⟩
  exact PrimitiveSocleYSectionSmallActionExclusion.not_y_section_of_degree_lt_twentySeven
    D s e (by simpa only [Nat.card_fin] using (show n<27 by omega))

theorem refine_original_nonaffine
    (h : BoundedSharpTitsCompleteActualResidual.OriginalNonaffineSporadicResidual J) :
    OriginalNonaffineSporadicResidual J := by
  obtain ⟨ht,hr⟩ := h
  letI := ht
  obtain ⟨x₀,block,hdegree,D,s,⟨e⟩,hglobal⟩ := hr
  refine ⟨ht,x₀,block,hdegree,D,s,⟨e⟩,hglobal,?_⟩
  exact PrimitiveSocleYSectionSmallActionExclusion.not_y_section_of_degree_lt_twentySeven
    D s e (by omega)

theorem genRank_le_sharpFloor_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (hlo : 4≤n) (hhi : n≤21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases BoundedSharpTenClosedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hCFSG hlo hhi ht with hpaid | hp | hb
  · exact Or.inl hpaid
  · exact Or.inr (Or.inl (refine_primitive J hhi hp))
  · exact Or.inr (Or.inr (refine_original_nonaffine J hb))

theorem exists_generating_finset_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (hlo : 4≤n) (hhi : n≤21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    (∃ U : Finset J,Subgroup.closure (U : Set J)=⊤ ∧ U.card ≤ sharpFloor n) ∨
      ActualResidual J := by
  rcases genRank_le_sharpFloor_or_actual_residual J hCFSG hlo hhi ht with hpaid | hbad
  · obtain ⟨U,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨U,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr hbad

end SymmetricSubgroupAsymptotics.BoundedSharpTenClosedYExcludedActualResidual
