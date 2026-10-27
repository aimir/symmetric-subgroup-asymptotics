import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers
import Mathlib.Data.Fintype.EquivFin

/-! A literal tuple of length equal to the actual ordinary generating rank. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ActualRankGeneratingTuple

theorem exists_tuple (G : Type) [Group G] [Finite G] :
    ∃ f : Fin (MarkedC4.genRank G) → G,Subgroup.closure (Set.range f)=⊤ := by
  obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := G)
  let eS : S ≃ Fin (MarkedC4.genRank G) := S.equivFinOfCardEq hcard
  let f : Fin (MarkedC4.genRank G) → G := fun i => (eS.symm i : G)
  have hrange : Set.range f=(S : Set G) := by
    ext g
    constructor
    · rintro ⟨i,rfl⟩
      exact (eS.symm i).property
    · intro hg
      refine ⟨eS ⟨g,hg⟩,?_⟩
      exact congrArg (fun z : S => (z : G)) (eS.symm_apply_apply ⟨g,hg⟩)
  have hf : Subgroup.closure (Set.range f)=⊤ := by rw [hrange]; exact hgen
  exact ⟨f,hf⟩

end SymmetricSubgroupAsymptotics.ActualRankGeneratingTuple
