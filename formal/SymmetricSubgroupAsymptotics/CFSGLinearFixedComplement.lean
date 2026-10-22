import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Module

/-! A linear complement fixed by three actual operators extends a power
identity from two distinguished columns to any additional column. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGLinearFixedComplement
variable {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

theorem complement_fixed (p q t : Module.End K M) (x u v e : M) (a b : K)
    (hpx : p x=x+a • e) (hpu : p u=u) (hpv : p v=v+e)
    (hqx : q x=x+a • u) (hqu : q u=u) (hqv : q v=v+u)
    (htx : t x=x+b • v) (htu : t u=u+v) (htv : t v=v) :
    (p*q*t) (x-b • u-a • v)=x-b • u-a • v := by
  have ht : t (x-b • u-a • v)=x-b • u-a • v := by
    rw [map_sub,map_sub,map_smul,map_smul,htx,htu,htv]
    module
  have hq : q (x-b • u-a • v)=x-b • u-a • v := by
    rw [map_sub,map_sub,map_smul,map_smul,hqx,hqu,hqv]
    module
  have hp : p (x-b • u-a • v)=x-b • u-a • v := by
    rw [map_sub,map_sub,map_smul,map_smul,hpx,hpu,hpv]
    module
  simp only [Module.End.mul_apply,ht,hq,hp]

theorem power_fixed_of_complement (f : Module.End K M) (k : ℕ)
    (x u v : M) (a b : K) (hc : f (x-b • u-a • v)=x-b • u-a • v)
    (hu : (f^k) u=u) (hv : (f^k) v=v) : (f^k) x=x := by
  have hc_all : ∀ l : ℕ, (f^l) (x-b • u-a • v)=x-b • u-a • v := by
    intro l
    induction l with
    | zero => rfl
    | succ l hl =>
      rw [pow_succ,Module.End.mul_apply,hc,hl]
  have hck := hc_all k
  have hx : x=(x-b • u-a • v)+b • u+a • v := by module
  calc
    (f^k) x=(f^k) ((x-b • u-a • v)+b • u+a • v) := congrArg (f^k) hx
    _=(x-b • u-a • v)+b • u+a • v := by
      rw [map_add,map_add,map_smul,map_smul,hck,hu,hv]
    _=x := hx.symm

end SymmetricSubgroupAsymptotics.CFSGLinearFixedComplement
