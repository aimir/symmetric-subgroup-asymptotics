import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Tactic.Module

/-! A characteristic-independent noncommuting image witness on a literal
three-string. Its detected coefficient is one, so the proof does not lose
the witness in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticThreeStringNoncentral
variable {K V : Type*} [CommRing K] [Nontrivial K] [AddCommGroup V] [Module K V]

theorem conjugated_root_not_fixed
    (U W : V≃ₗ[K]V) (e : Module.End K V) (u p m : V) (l : V→ₗ[K]K)
    (hUu : U u=u+(2:K) • p) (hUp : U p=p) (hUm : U m=m+u+p)
    (hWu : W u= -u) (hWp : W p=m) (hWm : W m=p)
    (heu : e u=(2:K) • p) (hep : e p=0) (hem : e m=u)
    (hlu : l u=1) (hlm : l m=0) :
    U.toLinearMap*(W.toLinearMap*e*W.symm.toLinearMap)*U.symm.toLinearMap≠
      W.toLinearMap*e*W.symm.toLinearMap := by
  have hUi : U.symm m=m-u+p := by
    apply U.injective
    simp only [LinearEquiv.apply_symm_apply,map_add,map_sub,hUm,hUu,hUp]
    module
  have hWiP : W.symm p=m := by
    apply W.injective
    rw [LinearEquiv.apply_symm_apply,hWm]
  have hWiM : W.symm m=p := by
    apply W.injective
    rw [LinearEquiv.apply_symm_apply,hWp]
  have hWiU : W.symm u= -u := by
    apply W.injective
    simp only [LinearEquiv.apply_symm_apply,map_neg,hWu,neg_neg]
  let Y : Module.End K V := W.toLinearMap*e*W.symm.toLinearMap
  have hYp : Y p= -u := by
    simp only [Y,Module.End.mul_apply,LinearEquiv.coe_coe,hWiP,hem,hWu]
  have hYm : Y m=0 := by
    simp only [Y,Module.End.mul_apply,LinearEquiv.coe_coe,hWiM,hep,map_zero]
  have hYu : Y u= -(2:K) • m := by
    simp only [Y,Module.End.mul_apply,LinearEquiv.coe_coe,hWiU,map_neg,heu,map_smul,hWp]
    module
  intro h
  change U.toLinearMap*Y*U.symm.toLinearMap=Y at h
  have hYui : Y (U.symm m)=(2:K) • m-u := by
    rw [hUi,map_add,map_sub,hYm,hYu,hYp]
    module
  have hv := DFunLike.congr_fun h m
  change U (Y (U.symm m))=Y m at hv
  rw [hYui,hYm] at hv
  have hz : u+(2:K) • m=0 := by
    calc
      _=U ((2:K) • m-u) := by
        rw [map_sub,map_smul,hUm,hUu]
        module
      _=0 := hv
  have hh := congrArg l hz
  simp only [map_add,map_smul,map_zero,hlu,hlm,smul_zero,add_zero] at hh
  exact one_ne_zero hh

end SymmetricSubgroupAsymptotics.CFSGQuadraticThreeStringNoncentral
