import SymmetricSubgroupAsymptotics.RepresentationModuleGeneratorTransport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
 theorem UniformSubrepresentationGeneratorBound.of_operator_containment
    {k G H V : Type} [Field k] [Group G] [Group H] [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (sigma : Representation k H V)
    (hoperator : ∀ h : H,∃ a : k[G],sigma h=rho.asAlgebraHom a)
    {n : ℕ} (hsigma : UniformSubrepresentationGeneratorBound sigma n) :
    UniformSubrepresentationGeneratorBound rho n := by
  intro W
  let S : Subrepresentation sigma := {
    toSubmodule := W.toSubmodule
    apply_mem_toSubmodule h v hv := by
      obtain ⟨a,ha⟩ := hoperator h
      rw [ha]
      exact W.asSubmodule.smul_mem a hv }
  obtain ⟨v,hv⟩ := hsigma S
  let code : Fin n → W.toRepresentation.asModule := fun i => ⟨(v i).val,(v i).property⟩
  let wi : W.toRepresentation.IntertwiningMap rho := {
    toLinearMap := W.toSubmodule.subtype
    isIntertwining' := fun _ => rfl }
  let wmap := Representation.IntertwiningMap.equivLinearMapAsModule W.toRepresentation rho wi
  let si : S.toRepresentation.IntertwiningMap sigma := {
    toLinearMap := S.toSubmodule.subtype
    isIntertwining' := fun _ => rfl }
  let smap := Representation.IntertwiningMap.equivLinearMapAsModule S.toRepresentation sigma si
  let P := Submodule.span k[G] (Set.range code)
  let U : Subrepresentation sigma := {
    toSubmodule := (P.map wmap).restrictScalars k
    apply_mem_toSubmodule h x hx := by
      obtain ⟨a,ha⟩ := hoperator h
      rw [ha]
      exact (P.map wmap).smul_mem a hx }
  have hgen : Submodule.span k[H] (Set.range v)≤U.asSubmodule.comap smap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨code i,Submodule.subset_span (Set.mem_range_self i),rfl⟩
  rw [hv] at hgen
  refine ⟨code,top_unique ?_⟩
  intro x _
  have hx : (⟨x.val,x.property⟩ : S.toRepresentation.asModule)∈U.asSubmodule.comap smap :=
    hgen Submodule.mem_top
  obtain ⟨y,hy,he⟩ := hx
  have hxy : y=x := Subtype.ext he
  exact hxy ▸ hy
end SymmetricSubgroupAsymptotics
