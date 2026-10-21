import SymmetricSubgroupAsymptotics.CFSGSylowCenterRecognition

/-! Every element of any Sylow centre is an actual inner conjugate of
an element in the centre of a fixed Sylow. The element and subgroup
isomorphism use the same Sylow conjugator. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSylowCenterRecognition
variable {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]

theorem exists_conjugate_fixed_sylow_center (P : Sylow p G) {x : G}
    (hx : x∈sylowCenterElements (G:=G) p) :
    ∃g : G,∃z : P,z∈Subgroup.center P ∧ g*(z : G)*g⁻¹=x := by
  obtain ⟨Q,y,hy,hyx⟩ := hx
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P Q
  subst Q
  let e : P≃*(g • P : Sylow p G) := P.equivSMul g
  let z : P := e.symm y
  have hz : z∈Subgroup.center P :=
    ((Subgroup.centerCongr e).symm ⟨y,hy⟩).property
  refine ⟨g,z,hz,?_⟩
  have he := congrArg (fun a : (g • P : Sylow p G) => (a : G)) (e.apply_symm_apply y)
  change g*(z : G)*g⁻¹=(y : G) at he
  exact he.trans hyx

theorem one_mem_sylowCenterElements : (1 : G)∈sylowCenterElements (G:=G) p := by
  let P : Sylow p G := Classical.choice (inferInstance : Nonempty (Sylow p G))
  exact ⟨P,1,(Subgroup.center P).one_mem,rfl⟩

end SymmetricSubgroupAsymptotics.CFSGSylowCenterRecognition
