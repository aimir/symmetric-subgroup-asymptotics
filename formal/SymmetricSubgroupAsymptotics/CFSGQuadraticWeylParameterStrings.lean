import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Parameterized rank-one word calculations on literal quadratic
strings, without division by two. They apply in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticWeylParameterStrings
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

def word (U V : K→Module.End K M) (t : Kˣ) : Module.End K M :=
  U (t:K)*V (-(t:K)⁻¹)*U (t:K)

theorem word_fixed (U V : K→Module.End K M) (t : Kˣ) (x : M)
    (hU : ∀a,U a x=x) (hV : ∀a,V a x=x) : word U V t x=x := by
  simp only [word,Module.End.mul_apply,hU,hV]

theorem word_pair (U V : K→Module.End K M) (t : Kˣ) (x y : M)
    (hUx : ∀a,U a x=x+a • y) (hUy : ∀a,U a y=y)
    (hVx : ∀a,V a x=x) (hVy : ∀a,V a y=y+a • x) :
    word U V t x=(t:K) • y ∧ word U V t y= -((t:K)⁻¹) • x := by
  constructor <;>
    simp only [word,Module.End.mul_apply,hUx,hUy,hVx,hVy,map_add,map_smul] <;>
    match_scalars <;> field_simp [Units.ne_zero t] <;> ring

theorem word_triple (U V : K→Module.End K M) (t : Kˣ) (u p m : M)
    (hUu : ∀a,U a u=u+(2*a) • p) (hUp : ∀a,U a p=p)
    (hUm : ∀a,U a m=m+a • u+a^2 • p)
    (hVu : ∀a,V a u=u+(2*a) • m)
    (hVp : ∀a,V a p=p+a • u+a^2 • m) (hVm : ∀a,V a m=m) :
    word U V t u= -u ∧ word U V t p=((t:K)⁻¹)^2 • m ∧
      word U V t m=(t:K)^2 • p := by
  constructor
  · simp only [word,Module.End.mul_apply,hUu,hUp,hUm,hVu,hVp,hVm,map_add,map_smul]
    match_scalars <;> field_simp [Units.ne_zero t] <;> ring
  · constructor <;>
      simp only [word,Module.End.mul_apply,hUu,hUp,hUm,hVu,hVp,hVm,map_add,map_smul] <;>
      match_scalars <;> field_simp [Units.ne_zero t] <;> ring

theorem word_cartan (U V : K→Module.End K M) (t : Kˣ) (u p m z : M) (c : K)
    (hUu : ∀a,U a u=u+(2*a) • p) (hUp : ∀a,U a p=p)
    (hUm : ∀a,U a m=m+a • u+a^2 • p)
    (hVu : ∀a,V a u=u+(2*a) • m)
    (hVp : ∀a,V a p=p+a • u+a^2 • m) (hVm : ∀a,V a m=m)
    (hUz : ∀a,U a z=z+(a*c) • p) (hVz : ∀a,V a z=z+(a*c) • m) :
    word U V t z=z-c • u := by
  simp only [word,Module.End.mul_apply,hUu,hUp,hUm,hVu,hVp,hVm,hUz,hVz,map_add,map_smul]
  match_scalars <;> field_simp [Units.ne_zero t] <;> ring

end SymmetricSubgroupAsymptotics.CFSGQuadraticWeylParameterStrings
