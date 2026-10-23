import SymmetricSubgroupAsymptotics.CFSGInvolutionNormImageAction
import Mathlib.Algebra.Module.Submodule.EqLocus
import Mathlib.LinearAlgebra.Quotient.Basic

/-! An action commuting with P descends to the literal fixed-space
quotient by the embedded norm image. No faithfulness is asserted.
For an involution, the embedded norm image is all of range(1+P). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGInvolutionFixedNormQuotientAction
open CFSGInvolutionNormImageAction
variable {R M:Type*} [CommRing R] [AddCommGroup M] [Module R M]

def fixedSubmodule (P:M→ₗ[R]M) : Submodule R M :=
  LinearMap.eqLocus P LinearMap.id

def normSubmodule (P:M→ₗ[R]M) : Submodule R (fixedSubmodule P) :=
  (normImage P).comap (fixedSubmodule P).subtype

private theorem inverse_commutes (P:M→ₗ[R]M) (f:M≃ₗ[R]M)
    (hc:∀x,f (P x)=P (f x)) : ∀x,f.symm (P x)=P (f.symm x) := by
  intro x
  apply f.injective
  rw [LinearEquiv.apply_symm_apply,hc,LinearEquiv.apply_symm_apply]

private theorem map_mem_fixed (P:M→ₗ[R]M) (f:M≃ₗ[R]M)
    (hc:∀x,f (P x)=P (f x)) (x:fixedSubmodule P) : f x.val∈fixedSubmodule P := by
  change P (f x.val)=f x.val
  rw [←hc]
  exact congrArg f x.property

def fixedRestriction (P:M→ₗ[R]M) (f:M≃ₗ[R]M) (hc:∀x,f (P x)=P (f x)) :
    fixedSubmodule P≃ₗ[R]fixedSubmodule P where
  toFun x:=⟨f x.val,map_mem_fixed P f hc x⟩
  invFun x:=⟨f.symm x.val,map_mem_fixed P f.symm (inverse_commutes P f hc) x⟩
  left_inv x:=Subtype.ext (f.symm_apply_apply x.val)
  right_inv x:=Subtype.ext (f.apply_symm_apply x.val)
  map_add' x y:=Subtype.ext (map_add f x.val y.val)
  map_smul' a x:=Subtype.ext (map_smul f a x.val)

theorem fixedRestriction_val (P:M→ₗ[R]M) (f:M≃ₗ[R]M) (hc:∀x,f (P x)=P (f x))
    (x:fixedSubmodule P) : (fixedRestriction P f hc x).val=f x.val := rfl

theorem fixedRestriction_map_norm (P:M→ₗ[R]M) (f:M≃ₗ[R]M) (hc:∀x,f (P x)=P (f x)) :
    (normSubmodule P).map (fixedRestriction P f hc).toLinearMap=normSubmodule P := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x,hx,rfl⟩:=Submodule.mem_map.mp hy
    change f x.val∈normImage P
    exact map_mem_normImage P f.toLinearMap hc x.val hx
  · intro y hy
    apply Submodule.mem_map.mpr
    refine ⟨(fixedRestriction P f hc).symm y,?_,(fixedRestriction P f hc).apply_symm_apply y⟩
    change f.symm y.val∈normImage P
    exact map_mem_normImage P f.symm.toLinearMap (inverse_commutes P f hc) y.val hy

def quotientRestriction (P:M→ₗ[R]M) (f:M≃ₗ[R]M) (hc:∀x,f (P x)=P (f x)) :
    (fixedSubmodule P ⧸ normSubmodule P)≃ₗ[R](fixedSubmodule P ⧸ normSubmodule P) :=
  Submodule.Quotient.equiv (normSubmodule P) (normSubmodule P)
    (fixedRestriction P f hc) (fixedRestriction_map_norm P f hc)

theorem quotientRestriction_mk (P:M→ₗ[R]M) (f:M≃ₗ[R]M) (hc:∀x,f (P x)=P (f x))
    (x:fixedSubmodule P) :
    quotientRestriction P f hc (Submodule.Quotient.mk x)=
      Submodule.Quotient.mk (fixedRestriction P f hc x) := rfl

def quotientAction {G:Type*} [Group G] (P:M→ₗ[R]M) (rho:G→*(M≃ₗ[R]M))
    (hc:∀g x,rho g (P x)=P (rho g x)) :
    G→*((fixedSubmodule P ⧸ normSubmodule P)≃ₗ[R](fixedSubmodule P ⧸ normSubmodule P)) where
  toFun g:=quotientRestriction P (rho g) (hc g)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    refine Submodule.Quotient.induction_on _ x ?_
    intro v
    change Submodule.Quotient.mk (fixedRestriction P (rho 1) (hc 1) v)=Submodule.Quotient.mk v
    congr 1
    apply Subtype.ext
    change rho 1 v.val=v.val
    rw [map_one]
    rfl
  map_mul' g h:=by
    apply LinearEquiv.ext
    intro x
    refine Submodule.Quotient.induction_on _ x ?_
    intro v
    change Submodule.Quotient.mk (fixedRestriction P (rho (g*h)) (hc (g*h)) v)=
      Submodule.Quotient.mk (fixedRestriction P (rho g) (hc g) (fixedRestriction P (rho h) (hc h) v))
    congr 1
    apply Subtype.ext
    change rho (g*h) v.val=rho g (rho h v.val)
    rw [map_mul]
    rfl

theorem quotientAction_mk {G:Type*} [Group G] (P:M→ₗ[R]M) (rho:G→*(M≃ₗ[R]M))
    (hc:∀g x,rho g (P x)=P (rho g x)) (g:G) (x:fixedSubmodule P) :
    quotientAction P rho hc g (Submodule.Quotient.mk x)=
      Submodule.Quotient.mk (fixedRestriction P (rho g) (hc g) x) := rfl

end SymmetricSubgroupAsymptotics.CFSGInvolutionFixedNormQuotientAction
