import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! A power of a finite sum of linear operators vanishes on a vector
when every operator word of that length vanishes there. No commuting
operator assumption is imposed and no large multinomial is expanded. -/
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFiniteEndomorphismWords
variable {J R M : Type*} [Fintype J] [CommRing R] [AddCommGroup M] [Module R M]

def applyWord (T : J→Module.End R M) : List J→M→M
  | [],x=>x
  | i::w,x=>T i (applyWord T w x)

omit [Fintype J] in
theorem applyWord_append (T : J→Module.End R M) (v w : List J) (x : M) :
    applyWord T (v++w) x=applyWord T v (applyWord T w x) := by
  induction v with
  | nil=>rfl
  | cons i v ih=>simp only [List.cons_append,applyWord,ih]

theorem sum_pow_apply_eq_zero_of_words (T : J→Module.End R M) (n : ℕ) (x : M)
    (h : ∀w : List J,w.length=n→applyWord T w x=0) :
    ((∑i,T i)^n) x=0 := by
  induction n generalizing x with
  | zero=>simpa only [pow_zero,Module.End.one_apply] using h [] rfl
  | succ n ih=>
    rw [pow_succ,Module.End.mul_apply,LinearMap.sum_apply,map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    apply ih (T i x)
    intro w hw
    have hh := h (w++[i]) (by simp only [List.length_append,List.length_singleton,hw])
    simpa only [applyWord_append,applyWord] using hh

end SymmetricSubgroupAsymptotics.CFSGFiniteEndomorphismWords
