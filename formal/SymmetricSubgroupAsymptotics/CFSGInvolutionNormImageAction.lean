import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Algebra.Module.Submodule.Range

/-! Commuting linear actions restrict to the actual image of 1+P.
For an involution this image lies in its fixed space. No faithfulness
or dimension assertion is part of this construction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGInvolutionNormImageAction
variable {R M:Type*} [CommRing R] [AddCommGroup M] [Module R M]

def normImage (P:M→ₗ[R]M) : Submodule R M := (LinearMap.id+P).range

theorem normImage_generator (P:M→ₗ[R]M) (x:M) : x+P x∈normImage P := ⟨x,rfl⟩

theorem normImage_fixed (P:M→ₗ[R]M) (hP:Function.Involutive P)
    (x:normImage P) : P x.val=x.val := by
  obtain ⟨y,hy⟩ := x.property
  change y+P y=x.val at hy
  rw [←hy,map_add,hP,add_comm]

theorem map_mem_normImage (P:M→ₗ[R]M) (f:M→ₗ[R]M)
    (hc:∀x,f (P x)=P (f x)) (x:M) (hx:x∈normImage P) : f x∈normImage P := by
  obtain ⟨y,hy⟩ := hx
  change y+P y=x at hy
  refine ⟨f y,?_⟩
  change f y+P (f y)=f x
  rw [←hc,←map_add,hy]

private theorem inverse_commutes (P:M→ₗ[R]M) (f:M≃ₗ[R]M)
    (hc:∀x,f (P x)=P (f x)) : ∀x,f.symm (P x)=P (f.symm x) := by
  intro x
  apply f.injective
  rw [LinearEquiv.apply_symm_apply,hc,LinearEquiv.apply_symm_apply]

def restrictEquiv (P:M→ₗ[R]M) (f:M≃ₗ[R]M) (hc:∀x,f (P x)=P (f x)) :
    normImage P≃ₗ[R]normImage P where
  toFun x:=⟨f x.val,map_mem_normImage P f.toLinearMap hc x.val x.property⟩
  invFun x:=⟨f.symm x.val,map_mem_normImage P f.symm.toLinearMap
    (inverse_commutes P f hc) x.val x.property⟩
  left_inv x:=Subtype.ext (f.symm_apply_apply x.val)
  right_inv x:=Subtype.ext (f.apply_symm_apply x.val)
  map_add' x y:=Subtype.ext (map_add f x.val y.val)
  map_smul' a x:=Subtype.ext (map_smul f a x.val)

theorem restrictEquiv_val (P:M→ₗ[R]M) (f:M≃ₗ[R]M) (hc:∀x,f (P x)=P (f x))
    (x:normImage P) : (restrictEquiv P f hc x).val=f x.val := rfl

def normImageAction {G:Type*} [Group G] (P:M→ₗ[R]M) (rho:G→*(M≃ₗ[R]M))
    (hc:∀g x,rho g (P x)=P (rho g x)) : G→*(normImage P≃ₗ[R]normImage P) where
  toFun g:=restrictEquiv P (rho g) (hc g)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change rho 1 x.val=x.val
    rw [map_one]
    rfl
  map_mul' g h:=by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change rho (g*h) x.val=rho g (rho h x.val)
    rw [map_mul]
    rfl

theorem normImageAction_val {G:Type*} [Group G] (P:M→ₗ[R]M) (rho:G→*(M≃ₗ[R]M))
    (hc:∀g x,rho g (P x)=P (rho g x)) (g:G) (x:normImage P) :
    (normImageAction P rho hc g x).val=rho g x.val := rfl

end SymmetricSubgroupAsymptotics.CFSGInvolutionNormImageAction
