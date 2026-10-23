import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Opposite-root intertwining detects the inverse relation in a
literal quadratic adjoint string, including characteristic two. Only
one coefficient-one Cartan functional is used; division by two and a
faithful natural two-dimensional representation are unnecessary. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticRankOneIntertwiner
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

def tripleWord (U V : K→Module.End K M) (a b : K) : Module.End K M := U a*V b*U a

theorem tripleWord_positive (U V : K→Module.End K M) (u p m : M)
    (hUu : ∀a,U a u=u+(2*a) • p) (hUp : ∀a,U a p=p)
    (hUm : ∀a,U a m=m+a • u+a^2 • p)
    (hVp : ∀a,V a p=p+a • u+a^2 • m) (a b : K) :
    tripleWord U V a b p=(1+a*b)^2 • p+(b+a*b^2) • u+b^2 • m := by
  simp only [tripleWord,Module.End.mul_apply,hUp,hVp,map_add,map_smul,hUu,hUm]
  match_scalars <;> ring

theorem one_add_mul_eq_zero_of_intertwines
    (U V : K→Module.End K M) (u p m : M)
    (hUu : ∀a,U a u=u+(2*a) • p) (hUp : ∀a,U a p=p)
    (hUm : ∀a,U a m=m+a • u+a^2 • p)
    (hVu : ∀a,V a u=u+(2*a) • m)
    (hVp : ∀a,V a p=p+a • u+a^2 • m) (hVm : ∀a,V a m=m)
    (l : M→ₗ[K]K) (hlu : l u=1) (hlp : l p=0) (hlm : l m=0)
    (a b t s : K) (hs : s≠0)
    (hinter : tripleWord U V a b*U t=V s*tripleWord U V a b) :
    1+a*b=0 := by
  have hh := congrArg (fun L:Module.End K M=>L p) hinter
  simp only [Module.End.mul_apply,hUp,
    tripleWord_positive U V u p m hUu hUp hUm hVp] at hh
  have hc := congrArg l hh
  simp only [map_add,map_smul,hVu,hVp,hVm,hlu,hlp,hlm,
    smul_eq_mul,mul_zero,mul_one,zero_add,add_zero] at hc
  have hz : s*(1+a*b)^2=0 := by linear_combination -hc
  have hp : (1+a*b)^2=0 := (mul_eq_zero.mp hz).resolve_left hs
  exact mul_self_eq_zero.mp (by simpa only [pow_two] using hp)

end SymmetricSubgroupAsymptotics.CFSGQuadraticRankOneIntertwiner
