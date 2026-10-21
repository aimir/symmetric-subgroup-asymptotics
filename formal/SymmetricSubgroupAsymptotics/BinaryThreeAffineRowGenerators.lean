import SymmetricSubgroupAsymptotics.BinaryThreeAffineRowActions
import SymmetricSubgroupAsymptotics.GeneralThreeTwoRowGenerators
import SymmetricSubgroupAsymptotics.FiniteSubgroupJoinWords

/-! Eleven fixed original-point generators for each affine GL3 row. The
closure equality is structural, so later finite point-word bindings need
no affine-group cardinality or unproved row correspondence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryThreeAffineRowGenerators
open BinaryThreeAffineRowActions

def translationGenerators (j : Fin 8) : Ambient := translation (points.symm j)

def generators (i : Fin 15) (j : Fin 11) : Ambient :=
  Fin.addCases (m := 8) (n := 3) translationGenerators
    (fun k => linear (GeneralThreeTwoRowGenerators.generators i k)) j

theorem translations_eq_closure : translation.range =
    Subgroup.closure (Set.range translationGenerators) := by
  apply le_antisymm
  · rintro g ⟨v,rfl⟩
    have h : translationGenerators (points v) ∈
        Subgroup.closure (Set.range translationGenerators) :=
      Subgroup.subset_closure (Set.mem_range_self _)
    simpa only [translationGenerators,points.symm_apply_apply] using h
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨j,rfl⟩
    exact ⟨points.symm j,rfl⟩

theorem rows_eq_closure (i : Fin 15) : BinaryThreeAffineRowActions.rows i =
    Subgroup.closure (Set.range (generators i)) := by
  have hl : (GeneralThreeTwoActualSubgroupCoverage.rows i).map linear =
      Subgroup.closure (Set.range
        (fun k => linear (GeneralThreeTwoRowGenerators.generators i k))) := by
    rw [GeneralThreeTwoRowGenerators.rows_eq_closure,MonoidHom.map_closure,
      ←Set.range_comp']
  have hrange : Set.range (generators i) = Set.range translationGenerators ∪
      Set.range (fun k => linear (GeneralThreeTwoRowGenerators.generators i k)) := by
    ext g
    constructor
    · rintro ⟨j,rfl⟩
      refine Fin.addCases (m := 8) (n := 3) ?_ ?_ j
      · intro k
        exact Or.inl ⟨k,by simp only [generators,Fin.addCases_left]⟩
      · intro k
        exact Or.inr ⟨k,by simp only [generators,Fin.addCases_right]⟩
    · rintro (⟨j,rfl⟩ | ⟨j,rfl⟩)
      · exact ⟨Fin.castAdd 3 j,by simp only [generators,Fin.addCases_left]⟩
      · exact ⟨Fin.natAdd 8 j,by simp only [generators,Fin.addCases_right]⟩
  rw [BinaryThreeAffineRowActions.rows,affine,translations_eq_closure,hl,
    ←Subgroup.closure_union,←hrange]

end SymmetricSubgroupAsymptotics.BinaryThreeAffineRowGenerators
end
