import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! Two actual p-subgroups generating a finite group extend to two actual
conjugate Sylow subgroups generating the SAME group. Neither original
p-subgroup is assumed maximal and no ambient conjugator is assumed inner. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGTwoPSubgroupsSylowGeneration
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_conjugate_sylows (U V : Subgroup G) (hU : IsPGroup p U) (hV : IsPGroup p V)
    (hgen : U⊔V=⊤) : ∃ (P : Sylow p G) (g : G),U≤P ∧
      Subgroup.closure ((P : Set G) ∪ (P : Subgroup G).map (MulAut.conj g).toMonoidHom)=⊤ := by
  obtain ⟨P,hUP⟩ := hU.exists_le_sylow
  obtain ⟨Q,hVQ⟩ := hV.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P Q
  have he : (P : Subgroup G).map (MulAut.conj g).toMonoidHom=(Q : Subgroup G) := by
    have hh := congrArg (fun R : Sylow p G=>(R : Subgroup G)) hg
    simpa only [Sylow.smul_def,Sylow.pointwise_smul_def,Subgroup.pointwise_smul_def] using hh
  refine ⟨P,g,hUP,?_⟩
  let R := Subgroup.closure ((P : Set G) ∪ (P : Subgroup G).map (MulAut.conj g).toMonoidHom)
  have hUR : U≤R := by
    intro x hx
    exact Subgroup.subset_closure (Or.inl (hUP hx))
  have hVR : V≤R := by
    intro x hx
    apply Subgroup.subset_closure
    apply Or.inr
    rw [he]
    exact hVQ hx
  apply top_unique
  rw [←hgen]
  exact sup_le hUR hVR

end SymmetricSubgroupAsymptotics.CFSGTwoPSubgroupsSylowGeneration
