import Mathlib.LinearAlgebra.Center

/-! A linear map whose rays agree with those of a fixed embedding is
one scalar multiple of that embedding. This works with a proper ambient
codomain and does not assume a projective recognition theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGEmbeddedLinearRayScalar
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

theorem exists_scalar (e L : V→ₗ[K]W) (he : Function.Injective e)
    (h : ∀x : V,∃c : K,L x=c•e x) : ∃c : K,∀x : V,L x=c•e x := by
  let E := LinearEquiv.ofInjective e he
  let T : V→ₗ[K]e.range := L.codRestrict e.range (fun x=>by
    obtain ⟨c,hc⟩ := h x
    exact ⟨c•x,by rw [map_smul,hc]⟩)
  let D : V→ₗ[K]V := E.symm.toLinearMap.comp T
  have heD (x : V) : e (D x)=L x := by
    exact congrArg Subtype.val (E.apply_symm_apply (T x))
  have hD (x : V) : ∃c : K,D x=c•x := by
    obtain ⟨c,hc⟩ := h x
    refine ⟨c,he ?_⟩
    rw [heD,hc,map_smul]
  obtain ⟨c,hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f:=D) (fun x hli=>by
      obtain ⟨a,ha⟩ := hD x
      have hz : (-a)•x+(1 : K)•D x=0 := by rw [ha];simp
      exact one_ne_zero ((LinearIndependent.pair_iff.mp hli) (-a) 1 hz).2)
  refine ⟨c,fun x=>?_⟩
  rw [←heD,hc]
  exact e.map_smul c x

end SymmetricSubgroupAsymptotics.CFSGEmbeddedLinearRayScalar
