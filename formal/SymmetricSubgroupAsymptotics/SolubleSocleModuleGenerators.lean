import SymmetricSubgroupAsymptotics.SolubleSocleConjugationModule
import SymmetricSubgroupAsymptotics.SchurIsotypicGenerators
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing

/-! Integral conjugation-module generators become normal generators in
the original finite group, including mixed-prime socle summands. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.SolubleSocleConjugationModule

theorem normalGen_submoduleGroup_le_of_moduleGeneratedBy
    {G : Type} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [IsMulCommutative N]
    (S : Submodule ℤ[G] (representation N).asModule) (t : ℕ)
    (hgen : ModuleGeneratedBy ℤ[G] S t) :
    MarkedC4.normalGen (submoduleGroup N S)≤t := by
  obtain ⟨v,hv⟩ := hgen
  let g : Fin t → G := fun i => ((v i).val.toMul : G)
  let H : Subgroup G := Subgroup.normalClosure (Set.range g)
  have hS : S≤normalSubmodule N H := by
    intro y hy
    have hspan : Submodule.span ℤ[G] (Set.range v)≤
        (normalSubmodule N H).comap S.subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change g i∈H
      exact Subgroup.subset_normalClosure (Set.mem_range_self i)
    have hm : (⟨y,hy⟩ : S)∈Submodule.span ℤ[G] (Set.range v) := by
      rw [hv]
      trivial
    exact hspan hm
  have hclosure : H=submoduleGroup N S := by
    apply le_antisymm
    · apply Subgroup.normalClosure_le_normal
      rintro _ ⟨i,rfl⟩
      exact (mem_submoduleGroup N S (v i).val.toMul).mpr (v i).property
    · have hle := submoduleGroup_mono N hS
      rw [submoduleGroup_normalSubmodule N H (by
        apply Subgroup.normalClosure_le_normal
        rintro _ ⟨i,rfl⟩
        exact (v i).val.toMul.property)] at hle
      exact hle
  exact normalGen_le_of_fin_tuple g hclosure

end SymmetricSubgroupAsymptotics.SolubleSocleConjugationModule
