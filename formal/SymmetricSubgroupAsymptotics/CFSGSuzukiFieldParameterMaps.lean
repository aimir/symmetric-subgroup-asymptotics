import SymmetricSubgroupAsymptotics.CFSGSuzukiFieldParameters
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Explicit inverse scalar maps and the twist-minus-identity obstruction
used in the actual Suzuki torus and anisotropic norm computations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiFieldParameters

theorem inverseTheta_square (m : ℕ) (x : Field m) : (inverseTheta m x)^2=theta m x := by
  have he := theta_twice m (inverseTheta m x)
  rw [theta_inverseTheta] at he
  exact he.symm

theorem theta_ne_zero (m : ℕ) {x : Field m} (hx : x≠0) : theta m x≠0 := by
  intro he
  apply hx
  exact (theta_bijective m).1 (he.trans (map_zero (theta m)).symm)

def torusParameter (m : ℕ) (x : Field m) : Field m := x*inverseTheta m x
def inverseTorusParameter (m : ℕ) (x : Field m) : Field m := x^2/theta m x

theorem inverseTorusParameter_torusParameter (m : ℕ) (x : Field m) :
    inverseTorusParameter m (torusParameter m x)=x := by
  by_cases hx : x=0
  · simp [torusParameter,inverseTorusParameter,hx]
  · have ht := theta_ne_zero m hx
    dsimp only [torusParameter,inverseTorusParameter]
    rw [map_mul,theta_inverseTheta,mul_pow,inverseTheta_square]
    field_simp [hx,ht] <;> ring

theorem torusParameter_inverseTorusParameter (m : ℕ) (x : Field m) :
    torusParameter m (inverseTorusParameter m x)=x := by
  by_cases hx : x=0
  · simp [torusParameter,inverseTorusParameter,hx]
  · have ht := theta_ne_zero m hx
    dsimp only [torusParameter,inverseTorusParameter]
    rw [map_div₀,map_pow,inverseTheta_theta,inverseTheta_square]
    field_simp [hx,ht] <;> ring

def torusParameterEquiv (m : ℕ) : Field m ≃ Field m where
  toFun := torusParameter m
  invFun := inverseTorusParameter m
  left_inv := inverseTorusParameter_torusParameter m
  right_inv := torusParameter_inverseTorusParameter m

theorem torusParameter_bijective (m : ℕ) : Function.Bijective (torusParameter m) :=
  (torusParameterEquiv m).bijective

theorem torusParameter_eq_pow (m : ℕ) (x : Field m) :
    torusParameter m x=x^(1+2^m) := by
  simp only [torusParameter,inverseTheta_apply,pow_add,pow_one]

def thetaProduct (m : ℕ) (x : Field m) : Field m := x*theta m x
def thetaQuotient (m : ℕ) (x : Field m) : Field m := theta m x/x

theorem thetaQuotient_thetaProduct (m : ℕ) (x : Field m) :
    thetaQuotient m (thetaProduct m x)=x := by
  by_cases hx : x=0
  · simp [thetaProduct,thetaQuotient,hx]
  · have ht := theta_ne_zero m hx
    dsimp only [thetaProduct,thetaQuotient]
    rw [map_mul,theta_twice]
    field_simp [hx,ht] <;> ring

theorem thetaProduct_thetaQuotient (m : ℕ) (x : Field m) :
    thetaProduct m (thetaQuotient m x)=x := by
  by_cases hx : x=0
  · simp [thetaProduct,thetaQuotient,hx]
  · have ht := theta_ne_zero m hx
    dsimp only [thetaProduct,thetaQuotient]
    rw [map_div₀,theta_twice]
    field_simp [hx,ht] <;> ring

def thetaProductEquiv (m : ℕ) : Field m ≃ Field m where
  toFun := thetaProduct m
  invFun := thetaQuotient m
  left_inv := thetaQuotient_thetaProduct m
  right_inv := thetaProduct_thetaQuotient m

theorem thetaProduct_bijective (m : ℕ) : Function.Bijective (thetaProduct m) :=
  (thetaProductEquiv m).bijective

theorem thetaQuotient_bijective (m : ℕ) : Function.Bijective (thetaQuotient m) :=
  (thetaProductEquiv m).symm.bijective

theorem thetaProduct_eq_pow (m : ℕ) (x : Field m) :
    thetaProduct m x=x^(1+2^(m+1)) := by
  simp only [thetaProduct,theta_apply,pow_add,pow_one]

/-- The scalar equation whose absence makes the Suzuki norm anisotropic
has no solution in the original field, including the smallest parameter. -/
theorem theta_add_self_ne_one (m : ℕ) (x : Field m) : theta m x+x≠1 := by
  intro hx
  have ht : x^2+theta m x=1 := by
    have he := congrArg (theta m) hx
    simpa only [map_add,map_one,theta_twice] using he
  have he : x^2+theta m x=x+theta m x := ht.trans (by simpa only [add_comm] using hx.symm)
  have hs : x^2=x := add_right_cancel he
  have hz : x*(x-1)=0 := by rw [mul_sub,mul_one,←pow_two,hs,sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · subst x
    exact zero_ne_one (by simpa only [map_zero,zero_add] using hx)
  · have hx1 : x=1 := sub_eq_zero.mp h
    subst x
    exact zero_ne_one (by simpa only [map_one,CharTwo.add_self_eq_zero] using hx)

theorem theta_add_self_eq_zero_iff (m : ℕ) (x : Field m) :
    theta m x+x=0 ↔ x=0 ∨ x=1 := by
  rw [add_eq_zero_iff_eq_neg,CharTwo.neg_eq,theta_fixed_iff]

end SymmetricSubgroupAsymptotics.CFSGSuzukiFieldParameters
