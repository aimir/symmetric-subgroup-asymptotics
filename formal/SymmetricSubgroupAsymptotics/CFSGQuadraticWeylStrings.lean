import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.Module

/-! Exact rational quadratic Weyl-word calculations on strings of length
one, two, and three. The later lattice consumer supplies these columns
from its actual norm-two roots. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticWeylStrings
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

def exponential (e : Module.End ℚ V) (t : ℚ) : Module.End ℚ V :=
  1+t • e+(t^2/2) • (e*e)

def word (e f : Module.End ℚ V) : Module.End ℚ V :=
  exponential e 1*exponential f (-1)*exponential e 1

theorem exponential_apply (e : Module.End ℚ V) (t : ℚ) (x : V) :
    exponential e t x=x+t • e x+(t^2/2) • e (e x) := by
  simp only [exponential,LinearMap.add_apply,LinearMap.smul_apply,
    Module.End.one_apply,Module.End.mul_apply]

theorem word_fixed (e f : Module.End ℚ V) (x : V) (hex : e x=0) (hfx : f x=0) :
    word e f x=x := by
  simp [word,exponential_apply,Module.End.mul_apply,hex,hfx]

theorem word_pair (e f : Module.End ℚ V) (x y : V)
    (hex : e x=y) (hey : e y=0) (hfx : f x=0) (hfy : f y=x) :
    word e f x=y ∧ word e f y= -x := by
  constructor <;>
    simp [word,exponential_apply,Module.End.mul_apply,map_add,map_smul,
      hex,hey,hfx,hfy] <;> module

theorem word_triple (e f : Module.End ℚ V) (u p m : V)
    (heu : e u=(2:ℚ) • p) (hep : e p=0) (hem : e m=u)
    (hfu : f u=(2:ℚ) • m) (hfp : f p=u) (hfm : f m=0) :
    word e f u= -u ∧ word e f p=m ∧ word e f m=p := by
  constructor
  · simp [word,exponential_apply,Module.End.mul_apply,map_add,map_smul,
      heu,hep,hem,hfu,hfp,hfm] <;> module
  · constructor <;>
      simp [word,exponential_apply,Module.End.mul_apply,map_add,map_smul,
        heu,hep,hem,hfu,hfp,hfm] <;> module

theorem word_cartan (e f : Module.End ℚ V) (u p m v : V) (c : ℚ)
    (heu : e u=(2:ℚ) • p) (hep : e p=0) (hem : e m=u)
    (hfu : f u=(2:ℚ) • m) (hfp : f p=u) (hfm : f m=0)
    (hev : e v=c • p) (hfv : f v=c • m) :
    word e f v=v-c • u := by
  simp [word,exponential_apply,Module.End.mul_apply,map_add,map_smul,
    heu,hep,hem,hfu,hfp,hfm,hev,hfv] <;> module

theorem fourth_fixed (w : Module.End ℚ V) (x : V) (hx : w x=x) : (w^4) x=x := by
  simp only [pow_succ,pow_zero,Module.End.mul_apply,Module.End.one_apply,hx]

theorem fourth_pair (w : Module.End ℚ V) (x y : V) (hx : w x=y) (hy : w y= -x) :
    (w^4) x=x := by
  simp only [pow_succ,pow_zero,Module.End.mul_apply,Module.End.one_apply,hx,hy,map_neg,neg_neg]

theorem fourth_involution (w : Module.End ℚ V) (x y : V) (hx : w x=y) (hy : w y=x) :
    (w^4) x=x := by
  simp only [pow_succ,pow_zero,Module.End.mul_apply,Module.End.one_apply,hx,hy]

theorem fourth_cartan (w : Module.End ℚ V) (u v : V) (c : ℚ)
    (hu : w u= -u) (hv : w v=v-c • u) : (w^4) v=v := by
  have htwo : (w^2) v=v := by
    simp only [pow_two,Module.End.mul_apply,hv,map_sub,map_smul,hu]
    module
  rw [show 4=2+2 by rfl,pow_add,Module.End.mul_apply,htwo,htwo]

end SymmetricSubgroupAsymptotics.CFSGQuadraticWeylStrings
