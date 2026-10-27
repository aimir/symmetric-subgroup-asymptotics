import SymmetricSubgroupAsymptotics.BoundedSharpLargePrimePairsExcludedActualResidual
import SymmetricSubgroupAsymptotics.PrimitiveSocleMonsterSmallActionExclusion

/-! Preserve every large-prime-pair, Mathieu, J4 and Y exclusion, and all
original D/block witnesses, adding the actual Monster index27 exclusion.
Only degree/fibre<27 is used; no whole-Monster generation claim or new
model/numerical callback occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BoundedSharpMonsterExcludedActualResidual
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleYSectionOrdinaryTail OriginalAffineBoundedSharpCoTwoTopRefinement
open BoundedSharpMathieuAndJFourExcludedActualResidual (NewlyExcluded)
open PrimitiveSocleLargePrimePairBoundedSharp (LargePrimePairTag)
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

def PrimitiveSporadicResidual : Prop :=
  MulAction.IsPreprimitive J (Fin n) ∧
    ∃ D : NonaffineData J (Fin n), ∃ s : CFSG.Sporadic,
      Nonempty (D.Simple ≃* (CFSG.Index.sporadic s).Model) ∧
        (n ≤ 10 → ¬GlobalExcluded s) ∧ ¬IsYSectionModel s ∧
          ¬NewlyExcluded s ∧ ¬LargePrimePairTag s ∧ s ≠ .monster

def OriginalNonaffineSporadicResidual : Prop :=
  ∃ ht : MulAction.IsPretransitive J (Fin n),
    letI := ht
    ∃ x₀ : Fin n, ∃ block : OriginalMinimalBlock (A := J) x₀,
      Nat.card block.Fibre ≤ 10 ∧
        ∃ D : NonaffineData block.Component block.Fibre, ∃ s : CFSG.Sporadic,
          Nonempty (D.Simple ≃* (CFSG.Index.sporadic s).Model) ∧
            ¬GlobalExcluded s ∧ ¬IsYSectionModel s ∧ ¬NewlyExcluded s ∧
              ¬LargePrimePairTag s ∧ s ≠ .monster

def ActualResidual : Prop := PrimitiveSporadicResidual J ∨ OriginalNonaffineSporadicResidual J

theorem refine_primitive (hhi : n ≤ 21)
    (h : BoundedSharpLargePrimePairsExcludedActualResidual.PrimitiveSporadicResidual J) :
    PrimitiveSporadicResidual J := by
  obtain ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge⟩ := h
  refine ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,?_⟩
  intro hs
  subst s
  exact PrimitiveSocleMonsterSmallActionExclusion.not_monster_of_degree_lt_twentySeven
    D e (by simpa only [Nat.card_fin] using (show n < 27 by omega))

theorem refine_original_nonaffine
    (h : BoundedSharpLargePrimePairsExcludedActualResidual.OriginalNonaffineSporadicResidual J) :
    OriginalNonaffineSporadicResidual J := by
  obtain ⟨ht,hr⟩ := h
  letI := ht
  obtain ⟨x₀,block,hdegree,D,s,⟨e⟩,hglobal,hY,hnew,hlarge⟩ := hr
  refine ⟨ht,x₀,block,hdegree,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,?_⟩
  intro hs
  subst s
  exact PrimitiveSocleMonsterSmallActionExclusion.not_monster_of_degree_lt_twentySeven
    D e (by omega)

theorem genRank_le_sharpFloor_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases BoundedSharpLargePrimePairsExcludedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hCFSG hlo hhi ht with hpaid | hp | hb
  · exact Or.inl hpaid
  · exact Or.inr (Or.inl (refine_primitive J hhi hp))
  · exact Or.inr (Or.inr (refine_original_nonaffine J hb))

theorem exists_generating_finset_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    (∃ U : Finset J,Subgroup.closure (U : Set J)=⊤ ∧ U.card ≤ sharpFloor n) ∨
      ActualResidual J := by
  rcases genRank_le_sharpFloor_or_actual_residual J hCFSG hlo hhi ht with hpaid | hbad
  · obtain ⟨U,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨U,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr hbad

end SymmetricSubgroupAsymptotics.BoundedSharpMonsterExcludedActualResidual
