import SymmetricSubgroupAsymptotics.SolubleSocleModuleGenerators

/-! Joins and top transport through the literal integral conjugation
submodule/ambient-normal-subgroup correspondence. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.SolubleSocleConjugationModule

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] [IsMulCommutative N]

theorem submoduleGroup_le_iff
    (S : Submodule ℤ[G] (representation N).asModule)
    (H : Subgroup G) [H.Normal] : submoduleGroup N S ≤ H ↔ S ≤ normalSubmodule N H := by
  constructor
  · intro h x hx
    exact h ((mem_submoduleGroup N S x.toMul).mpr hx)
  · intro h g hg
    obtain ⟨n,hn,rfl⟩ := hg
    exact h hn

theorem submoduleGroup_sup
    (S T : Submodule ℤ[G] (representation N).asModule) :
    submoduleGroup N (S⊔T)=submoduleGroup N S⊔submoduleGroup N T := by
  apply le_antisymm
  · apply (submoduleGroup_le_iff N _ _).mpr
    apply sup_le
    · exact (submoduleGroup_le_iff N S _).mp le_sup_left
    · exact (submoduleGroup_le_iff N T _).mp le_sup_right
  · exact sup_le (submoduleGroup_mono N le_sup_left) (submoduleGroup_mono N le_sup_right)

theorem submoduleGroup_top :
    submoduleGroup N (⊤ : Submodule ℤ[G] (representation N).asModule)=N := by
  apply le_antisymm (submoduleGroup_le N ⊤)
  intro n hn
  exact (mem_submoduleGroup N ⊤ (⟨n,hn⟩ : N)).mpr trivial

end SymmetricSubgroupAsymptotics.SolubleSocleConjugationModule
